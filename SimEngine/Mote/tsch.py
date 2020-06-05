"""
"""
from __future__ import absolute_import
from __future__ import division

# =========================== imports =========================================

from builtins import str
from builtins import filter
from builtins import range
from builtins import object
from past.utils import old_div
import copy
from itertools import chain
import random

import netaddr

# Mote sub-modules
from . import MoteDefines as d
from SimEngine.Mote.sf import SchedulingFunctionMSF

# Simulator-wide modules
import SimEngine

# =========================== defines =========================================

# =========================== helpers =========================================

# =========================== body ============================================

# TODO : move constants on the right place of code
NPEB_MIN_PDR_UNDERGO_SYNCHRO = 0.6
NPEB_MAX_JM_UNDERGO_SYNCHRO = 7
NPEB_MAX_NEIGHBORS_TO_LISTEN = 3
RDM_CHANNEL_NEW_NPEB_CELL = True
NPEB_MAX_NBR_CYCLES = 10
NPEB_MIN_NBR_CYCLES = 1
NPEB_JM_THRESH_NBR_CYCLES = 10
NPEB_NON_ROOT_MIN_NBR_CYCLES = 2
NPEB_MAX_NEIGHBORS_ANNOUNCED = 3

DELAY_LOG_AFTER_EB = 60


class Tsch(object):

    def __init__(self, mote):

        # store params
        self.mote = mote

        # singletons (quicker access, instead of recreating every time)
        self.engine   = SimEngine.SimEngine.SimEngine()
        self.settings = SimEngine.SimSettings.SimSettings()
        self.log      = SimEngine.SimLog.SimLog().log

        # local variables
        self.slotframes       = {}
        self.txQueue          = []
        if self.settings.tsch_tx_queue_size >= 0:
            self.txQueueSize  = self.settings.tsch_tx_queue_size
        elif self.settings.tsch_tx_queue_size == -1:
            self.txQueueSize  = float('inf')
        else:
            raise ValueError(
                u'unsupported tx_queue_size: {0}'.format(
                    self.settings.tsch_tx_queue_size
                )
            )
        if self.settings.tsch_max_tx_retries >= 0:
            self.max_tx_retries = self.settings.tsch_max_tx_retries
        elif self.settings.tsch_max_tx_retries == -1:
            self.max_tx_retries = float('inf')
        else:
            raise ValueError(
                u'unsupported tsch_max_tx_retries: {0}'.format(
                    self.settings.tsch_max_tx_retries
                )
            )
        self.neighbor_table   = []
        self.pktToSend        = None
        self.waitingFor       = None
        self.active_cell      = None
        self.asnLastSync      = None
        self.isSync           = False
        self.join_proxy       = None
        self.iAmSendingEBs    = False
        self.clock            = Clock(self.mote)
        self.next_seqnum      = 0
        self.received_eb_list = {} # indexed by source mac address
        # backoff state
        self.backoff_exponent        = d.TSCH_MIN_BACKOFF_EXPONENT
        # pending bit
        self.pending_bit_enabled            = False
        self.args_for_next_pending_bit_task = None

        assert self.settings.phy_numChans <= len(d.TSCH_HOPPING_SEQUENCE)
        self.hopping_sequence = (
            d.TSCH_HOPPING_SEQUENCE[:self.settings.phy_numChans]
        )

        # install the default slotframe
        self.add_slotframe(
            slotframe_handle = 0,
            length           = self.settings.tsch_slotframeLength
        )

        # NPEBs
        self.current_EB_delay = d.TSCH_MAX_EB_DELAY
        self.NPtable = NPtable(self)  # Neighbor Propositions table
        self.scheduleNPEB = scheduleNPEB(self)  # Possible cells for NPEB sending each x cycles of slotframe
        self.channel_offset_next_NPEB = None  # keep a trace of the channel offset for next NPEB
        # starting to decrease cycles counters from start ensures keeping consistent state
        self.schedule_next_decr_cycles_NPEB()
        self.firstEBauthorization = False  # used to log stats 1 min after (NP)EB announces allowed
    #======================== public ==========================================

    # getters/setters

    def getIsSync(self):
        return self.isSync

    def setIsSync(self,val):
        # set
        self.isSync = val

        if self.isSync:
            # log
            # NPEB_modif
            self.log(
                SimEngine.SimLog.LOG_TSCH_SYNCED,
                {
                    u'_mote_id':   self.mote.id,
                    u'idle_listen': self.mote.radio.stats[u'idle_listen'],
                    u'tx_data_rx_ack': self.mote.radio.stats[u'tx_data_rx_ack'],
                    u'tx_data': self.mote.radio.stats[u'tx_data'],
                    u'rx_data_tx_ack': self.mote.radio.stats[u'rx_data_tx_ack'],
                    u'rx_data': self.mote.radio.stats[u'rx_data'],
                    u'sleep': self.mote.radio.stats[u'sleep']
                }
            )

            self.asnLastSync = self.engine.getAsn()
            if self.mote.dagRoot:
                # we don't need the timers
                pass
            else:
                self._start_keep_alive_timer()
                self._start_synchronization_timer()

            # start SF
            self.mote.sf.start()

            # transition: listeningForEB->active
            self.current_EB_delay = d.TSCH_MAX_EB_DELAY  # reset for next synchro if got desynchronized
            self.engine.removeFutureEvent(      # remove previously scheduled listeningForEB cells
                uniqueTag=(self.mote.id, u'_action_listeningForEB_cell')
            )
        else:
            # log
            self.log(
                SimEngine.SimLog.LOG_TSCH_DESYNCED,
                {
                    "_mote_id":   self.mote.id,
                }
            )
            # DAGRoot gets never desynchronized
            assert not self.mote.dagRoot

            self.stopSendingEBs()
            self.delete_minimal_cell()
            self.mote.sf.stop()
            self.mote.sixp.clear_transaction_table()
            self.mote.secjoin.setIsJoined(False)
            self.asnLastSync = None
            self.clock.desync()
            self._stop_keep_alive_timer()
            self._stop_synchronization_timer()
            self.txQueue = []
            self.received_eb_list = {}
            # we may have this timer task
            self.engine.removeFutureEvent(
                uniqueTag=(self.mote.id, u'tsch', u'wait_secjoin')
            )

            # transition: active->listeningForEB
            self.engine.removeFutureEvent(      # remove previously scheduled listeningForEB cells
                uniqueTag=(self.mote.id, u'_action_active_cell')
            )
            self.schedule_next_listeningForEB_cell()

    def get_busy_slots(self, slotframe_handle=0):
        if slotframe_handle in self.slotframes:
            return self.slotframes[slotframe_handle].get_busy_slots()
        else:
            return 0

    def get_available_slots(self, slotframe_handle=0):
        if slotframe_handle in self.slotframes:
            return self.slotframes[slotframe_handle].get_available_slots()
        else:
            return 0

    def get_cell(self, slot_offset, channel_offset, mac_addr, slotframe_handle=0):
        if slotframe_handle in self.slotframes:
            slotframe = self.slotframes[slotframe_handle]
            cells = slotframe.get_cells_by_slot_offset(slot_offset)
            for cell in cells:
                if (
                        (cell.channel_offset == channel_offset)
                        and
                        (cell.mac_addr == mac_addr)
                    ):
                    return cell
        return None

    def get_cells(self, mac_addr=None, slotframe_handle=None):
        if slotframe_handle:
            if slotframe_handle in self.slotframes:
                slotframe = self.slotframes[slotframe_handle]
                ret_val = slotframe.get_cells_by_mac_addr(mac_addr)
            else:
                ret_val = []
        else:
            ret_val = []
            for slotframe_handle in self.slotframes:
                slotframe = self.slotframes[slotframe_handle]
                ret_val += slotframe.get_cells_by_mac_addr(mac_addr)
        return ret_val

    def enable_pending_bit(self):
        self.pending_bit_enabled = True

    # slotframe
    def get_slotframe(self, slotframe_handle):
        if slotframe_handle in self.slotframes:
            return self.slotframes[slotframe_handle]
        else:
            return None

    def add_slotframe(self, slotframe_handle, length):
        assert slotframe_handle not in self.slotframes
        self.slotframes[slotframe_handle] = SlotFrame(
            mote_id          = self.mote.id,
            slotframe_handle = slotframe_handle,
            num_slots        = length
        )
        self.log(
            SimEngine.SimLog.LOG_TSCH_ADD_SLOTFRAME,
            {
                u'_mote_id'       : self.mote.id,
                u'slotFrameHandle': slotframe_handle,
                u'length'         : length
            }
        )

    def delete_slotframe(self, slotframe_handle):
        assert slotframe_handle in self.slotframes
        self.log(
            SimEngine.SimLog.LOG_TSCH_DELETE_SLOTFRAME,
            {
                u'_mote_id'       : self.mote.id,
                u'slotFrameHandle': slotframe_handle,
                u'length'         : self.slotframes[slotframe_handle].length
            }
        )
        del self.slotframes[slotframe_handle]

    # EB / Enhanced Beacon

    def startSendingEBs(self):
        self.iAmSendingEBs = True
        print self.engine.getAsn(), "- Mote", self.mote.id, " starts sending EBs and registers a NPEB cell"
        self.scheduleNPEB.clear()
        self.scheduleNPEB.auto_register_new_cell()
        if self.mote.dagRoot:
            self.scheduleNPEB.auto_register_new_cell()  # start with 2 cells to boost startup
        if self.firstEBauthorization is False:
            self.firstEBauthorization = True
            self.engine.scheduleIn(
                delay=DELAY_LOG_AFTER_EB,
                cb=self._log_radio_stats,
                uniqueTag=(self.mote.id, u'_log_radio_stats'),
                intraSlotOrder=d.INTRASLOTORDER_STARTSLOT,
            )


    def schedule_next_decr_cycles_NPEB(self):
        # At each slotframe iteration, decrease referenced current cycle assigned to each NPEB cell
        # Will be rescheduled by _action_decrease_cycles_NPEB at end of the current slotframe iteration just starting
        asn = self.engine.getAsn()
        sizeSF0 = self.get_slotframe(0).length
        asn_end_next_cycle = asn + sizeSF0 - (asn % sizeSF0)
        self.engine.scheduleAtAsn(
            asn              = asn_end_next_cycle,
            cb               = self._action_decrease_cycles_NPEB,
            uniqueTag        = (self.mote.id, u'_action_decrease_cycles_NPEB'),
            intraSlotOrder   = d.INTRASLOTORDER_STARTSLOT,
        )

    def stopSendingEBs(self):
        self.iAmSendingEBs = False
        print self.engine.getAsn(), "- Mote", self.mote.id, " stopped sending EBs and removes registered NPEB cells :", self.scheduleNPEB.NPEBcells
        # NPEBs should not be emitted anymore, stop decreasing cycles dropping the related event
        self.engine.removeFutureEvent((self.mote.id, u'_action_decrease_cycles_NPEB'))
        self.scheduleNPEB.clear()
        self.NPtable.clear()

    def schedule_next_listeningForEB_cell(self):

        assert not self.getIsSync()

        # schedule at next ASN
        self.engine.scheduleAtAsn(
            asn              = self.engine.getAsn()+1,
            cb               = self._action_listeningForEB_cell,
            uniqueTag        = (self.mote.id, u'_action_listeningForEB_cell'),
            intraSlotOrder   = d.INTRASLOTORDER_STARTSLOT,
        )

    def schedule_next_listeningForNPEB_cell(self, scheduleNPEB):
        # Considering a given announcement NPEB cell (by a neighbor likely) scheduled in x cycles, pass this mote
        # in an inactive state until the targeted slot. We are sure a joined mode will normally emit an NPEB on it,
        # but not sure that we will hear it (too far). So schedule the wake up and restart an active search period
        # to hear the NPEB and carry on listening if we didn't hear it.
        assert not self.getIsSync()

        ts_offset, ch_offset = scheduleNPEB[u'cell']
        curr_cycle = scheduleNPEB[u'curr_cycle']
        nbr_cycles = scheduleNPEB[u'nbr_cycles']

        # NPEB can be scheduled in several slotframe iterations bu we can get its exact ASN
        lenSF0 = self.get_slotframe(0).length
        asn = self.engine.getAsn()
        asn_start_curr_cycle = int(asn / lenSF0) * lenSF0
        current_ts = asn % lenSF0
        if curr_cycle == 0 and ts_offset <= current_ts:
            # The NPEB was already emitted in this cycle some timeslots before -> compute next
            asn_start_announce_cycle = asn_start_curr_cycle + nbr_cycles * lenSF0
        else:
            asn_start_announce_cycle = asn_start_curr_cycle + curr_cycle * lenSF0
        asn_timeslot_cell = asn_start_announce_cycle + ts_offset

        self.channel_offset_next_NPEB = ch_offset

        self.log(
            SimEngine.SimLog.LOG_TSCH_SLEEP_UNTIL_NEXT_NPEB,
            {
                u'_mote_id': self.mote.id,
                u'target_asn': asn_timeslot_cell,
                u'cycles_to_elapse': curr_cycle,
                u'target_cell': scheduleNPEB[u'cell']
            }
        )
        print self.engine.getAsn(), "- Mote", self.mote.id, " schedules waiting NPEB in engine cell", scheduleNPEB[u'cell'], " resulting in ASN", asn_timeslot_cell
        # schedule at ASN considering cycles to be elapsed until this particular EB
        self.engine.scheduleAtAsn(
            asn              = asn_timeslot_cell,
            cb               = self._action_listeningForNPEB_cell,
            uniqueTag        = (self.mote.id, u'_action_listeningForNPEB_cell'),
            intraSlotOrder   = d.INTRASLOTORDER_STARTSLOT,
        )

    def should_undergo_synchro_with_bestNP(self):
        # TODO : may also depend of the following proposed neighbor if there is one
        assert self.NPtable.bestNP
        bestNP_infos = self.NPtable.get_bestNP_entry()
        # Decisional process to know whether should stop searching best neighbor and undergo synchronization
        # with the current best found

        def is_pdr_sufficient():
            pdr = self.engine.connectivity._rssi_to_pdr(bestNP_infos[u'signal'])
            return pdr > NPEB_MIN_PDR_UNDERGO_SYNCHRO

        def is_jm_sufficient():
            return bestNP_infos[u'join_metric'] <= NPEB_MAX_JM_UNDERGO_SYNCHRO

        if not is_pdr_sufficient():
            return False

        if bestNP_infos[u'join_metric'] == 0:  # it is root, should synchro with it !
            return True

        if not is_jm_sufficient():
            return False

        if len(self.NPtable) >= 2:  # should have listened to more than only one neighbor (not only the bestNP itself)
            if not self.NPtable.is_still_neighbor_to_listen():
                    return True
        return False

    def retrieve_NPs_for_ACK(self, ack_dst):
        rank = self.mote.rpl.getDagRank()
        if rank is None:
            return None  # Node not already in topology

        # We announce propositions only in ACK addressed to child
        parent_ack_dst = self.engine.get_mote_by_mac_addr(ack_dst).rpl.getPreferredParent()
        if parent_ack_dst != self.mote.get_mac_addr():
            return None
        propositions = {
            u'join_metric': rank - 1,
            u'selfNPEB':    self.scheduleNPEB.get_as_NPEB_field(),
            u'neighbors':   self.NPtable.select_NPs_to_announce().items()
        }
        return propositions

    # minimal

    def add_minimal_cell(self):
        assert self.isSync

        # the minimal cell is allocated in slotframe 0
        self.addCell(
            slotOffset       = 0,
            channelOffset    = 0,
            neighbor         = None,
            cellOptions      = [
                d.CELLOPTION_TX,
                d.CELLOPTION_RX,
                d.CELLOPTION_SHARED
            ],
            slotframe_handle = 0,
            link_type        = d.LINKTYPE_ADVERTISING
        )

    def delete_minimal_cell(self):
        # the minimal cell should be allocated in slotframe 0
        self.deleteCell(
            slotOffset       = 0,
            channelOffset    = 0,
            neighbor         = None,
            cellOptions      = [
                d.CELLOPTION_TX,
                d.CELLOPTION_RX,
                d.CELLOPTION_SHARED
            ],
            slotframe_handle = 0
        )

    # schedule interface

    def addCell(
            self,
            slotOffset,
            channelOffset,
            neighbor,
            cellOptions,
            slotframe_handle=0,
            link_type = d.LINKTYPE_NORMAL
        ):

        assert isinstance(slotOffset, int)
        assert isinstance(channelOffset, int)
        assert isinstance(cellOptions, list)
        assert link_type not in [True, False]

        slotframe = self.slotframes[slotframe_handle]

        # add cell
        cell = Cell(
            slotOffset,
            channelOffset,
            cellOptions,
            neighbor,
            link_type
        )
        slotframe.add(cell)

        # reschedule the next active cell, in case it is now earlier
        if self.getIsSync():
            self._schedule_next_active_slot()

    def deleteCell(self, slotOffset, channelOffset, neighbor, cellOptions, slotframe_handle=0):
        assert isinstance(slotOffset, int)
        assert isinstance(channelOffset, int)
        assert isinstance(cellOptions, list)

        slotframe = self.slotframes[slotframe_handle]

        # find a target cell. if the cell is not scheduled, the following
        # raises an exception
        cell = self.get_cell(slotOffset, channelOffset, neighbor, slotframe_handle)
        assert cell.mac_addr == neighbor
        assert cell.options == cellOptions

        # delete cell
        slotframe.delete(cell)

        # reschedule the next active cell, in case it is now earlier
        if self.getIsSync():
            self._schedule_next_active_slot()

    # tx queue interface with upper layers

    @property
    def droppable_normal_packet_index(self):
        for rindex, packet in enumerate(reversed(self.txQueue)):
            if (
                    (packet[u'mac'][u'priority'] is False)
                    and
                    (self.pktToSend != packet)
                ):
                # return index of the packet
                return len(self.txQueue) - rindex - 1
        return None

    def enqueue(self, packet, priority=False):

        assert packet[u'type'] != d.PKT_TYPE_EB
        assert packet[u'type'] != d.PKT_TYPE_NPEB
        assert u'srcMac' in packet[u'mac']
        assert u'dstMac' in packet[u'mac']

        goOn = True

        # check there is space in txQueue
        assert len(self.txQueue) <= self.txQueueSize
        if (
                goOn
                and
                (len(self.txQueue) == self.txQueueSize)
                and
                (
                    (priority is False)
                    or
                    self.droppable_normal_packet_index is None
                )
            ):
            # my TX queue is full

            # drop
            self.mote.drop_packet(
                packet  = packet,
                reason  = SimEngine.SimLog.DROPREASON_TXQUEUE_FULL
            )

            # couldn't enqueue
            goOn = False

        # check that I have cell to transmit on
        if goOn:
            shared_tx_cells = [cell for cell in self.mote.tsch.get_cells(None) if d.CELLOPTION_TX in cell.options]
            dedicated_tx_cells = [cell for cell in self.mote.tsch.get_cells(packet[u'mac'][u'dstMac']) if d.CELLOPTION_TX in cell.options]
            if (
                    (len(shared_tx_cells) == 0)
                    and
                    (len(dedicated_tx_cells) == 0)
                ):
                # I don't have any cell to transmit on

                # drop
                self.mote.drop_packet(
                    packet  = packet,
                    reason  = SimEngine.SimLog.DROPREASON_NO_TX_CELLS,
                )

                # couldn't enqueue
                goOn = False

        # if I get here, everyting is OK, I can enqueue
        if goOn:
            # set retriesLeft which should be renewed at every hop
            packet[u'mac'][u'retriesLeft'] = self.max_tx_retries
            # put the seqnum
            packet[u'mac'][u'seqnum'] = self.next_seqnum
            self.next_seqnum += 1
            if self.next_seqnum > 255:
                # sequence number field is 8-bit long
                self.next_seqnum = 0
            if priority:
                # mark priority to this packet
                packet[u'mac'][u'priority'] = True
                # if the queue is full, we need to drop the last one
                # in the queue or the new packet
                if len(self.txQueue) == self.txQueueSize:
                    assert not self.txQueue[-1][u'mac'][u'priority']
                    # drop the last one in the queue
                    packet_index_to_drop = self.droppable_normal_packet_index
                    packet_to_drop = self.dequeue_by_index(packet_index_to_drop)
                    self.mote.drop_packet(
                        packet = packet_to_drop,
                        reason  = SimEngine.SimLog.DROPREASON_TXQUEUE_FULL
                    )
                index = len(self.txQueue)
                for i, _ in enumerate(self.txQueue):
                    if self.txQueue[i][u'mac'][u'priority'] is False:
                        index = i
                        break
                self.txQueue.insert(index, packet)
            else:
                packet[u'mac'][u'priority'] = False
                # add to txQueue
                self.txQueue    += [packet]

        if (
                goOn
                and
                packet[u'mac'][u'dstMac'] != d.BROADCAST_ADDRESS
                and
                isinstance(self.mote.sf, SchedulingFunctionMSF)
                and
                not self.mote.sf.get_tx_cells(packet[u'mac'][u'dstMac'])
            ):
            # on-demand allocation of autonomous TX cell
            self.mote.sf.allocate_autonomous_tx_cell(
                packet[u'mac'][u'dstMac']
            )

        return goOn

    def dequeue(self, packet):
        if packet in self.txQueue:
            self.txQueue.remove(packet)
        else:
            # do nothing
            pass

        if (
                packet[u'mac'][u'dstMac'] != d.BROADCAST_ADDRESS
                and
                isinstance(self.mote.sf, SchedulingFunctionMSF)
                and
                not [
                    _pkt for _pkt in self.txQueue
                    if _pkt[u'mac'][u'dstMac'] == packet[u'mac'][u'dstMac']
                ]
                and
                self.mote.sf.get_autonomous_tx_cell(packet[u'mac'][u'dstMac'])
            ):
            # on-demand deallocation of autonomous TX cell
            self.mote.sf.deallocate_autonomous_tx_cell(
                packet[u'mac'][u'dstMac']
            )

    def dequeue_by_index(self, index):
        assert index < len(self.txQueue)
        return self.txQueue.pop(index)

    def get_first_packet_to_send(self, cell):
        assert cell
        dst_mac_addr = cell.mac_addr
        packet_to_send = None
        if dst_mac_addr is None:
            if self.scheduleNPEB.is_cell_registered(cell):
                # it is a scheduled cell to send NPEB this current cycle
                # we bypass self.mote.clear_to_send_EBs_DATA() to avoid interaction with specific SF
                packet_to_send = self._create_NPEB()
            elif (
                    len(self.txQueue) == 0
                    and
                    cell.link_type in [
                        d.LINKTYPE_ADVERTISING,
                        d.LINKTYPE_ADVERTISING_ONLY
                    ]
                ):
                # txQueue is empty; we may return an EB
                if self.mote.clear_to_send_EBs_DATA():
                    if self._decided_to_send_eb():
                        # normal EB sent with a probability depending neighbours
                        packet_to_send = self._create_EB()
                else:
                    packet_to_send = None
            else:
                # return the first one in the TX queue, whose destination MAC
                # is not associated with any of allocated (dedicated) TX cells
                for packet in self.txQueue:
                    packet_to_send = packet # tentatively
                    for _, slotframe in list(self.slotframes.items()):
                        dedicated_tx_cells = [cell for cell in slotframe.get_cells_by_mac_addr(packet[u'mac'][u'dstMac']) if d.CELLOPTION_TX in cell.options]
                        if len(dedicated_tx_cells) > 0:
                            packet_to_send = None
                            break # try the next packet in TX queue

                    if packet_to_send is not None:
                        # found a good packet to send
                        break

                # if no suitable packet is found, packet_to_send remains None
        else:
            for packet in self.txQueue:
                if packet[u'mac'][u'dstMac'] == dst_mac_addr:
                    # return the first one having the dstMac
                    packet_to_send = packet
                    break
            # if no packet is found, packet_to_send remains None

        return packet_to_send

    def get_num_packet_in_tx_queue(self, dst_mac_addr=None):
        if dst_mac_addr is None:
            return len(self.txQueue)
        else:
            return len(
                [
                    pkt for pkt in self.txQueue if (
                        pkt[u'mac'][u'dstMac'] == dst_mac_addr
                    )
                ]
            )

    def remove_packets_in_tx_queue(self, type, dstMac=None):
        i = 0
        while i < len(self.txQueue):
            if (
                    (self.txQueue[i][u'type'] == type)
                    and
                    (
                        (dstMac is None)
                        or
                        (self.txQueue[i][u'mac'][u'dstMac'] == dstMac)
                    )
                ):
                del self.txQueue[i]
            else:
                i += 1

    # interface with radio

    def txDone(self, isACKed, channel):
        assert isACKed in [True,False]

        asn         = self.engine.getAsn()
        active_cell = self.active_cell

        self.active_cell = None

        assert self.waitingFor == d.WAITING_FOR_TX

        # log
        self.log(
            SimEngine.SimLog.LOG_TSCH_TXDONE,
            {
                u'_mote_id':       self.mote.id,
                u'channel':        channel,
                u'slot_offset':    (
                    active_cell.slot_offset
                    if active_cell else None
                ),
                u'channel_offset': (
                    active_cell.channel_offset
                    if active_cell else None
                ),
                u'packet':         self.pktToSend,
                u'isACKed':        isACKed,
            }
        )

        if self.pktToSend[u'mac'][u'dstMac'] == d.BROADCAST_ADDRESS:
            # I just sent a broadcast packet

            assert self.pktToSend[u'type'] in [
                d.PKT_TYPE_EB,
                d.PKT_TYPE_NPEB,
                d.PKT_TYPE_DIO,
                d.PKT_TYPE_DIS
            ]
            assert isACKed == False

            # EBs are never in txQueue, no need to remove.
            if not(self.pktToSend[u'type'] in [d.PKT_TYPE_EB, d.PKT_TYPE_NPEB]):
                self.dequeue(self.pktToSend)

        else:
            # I just sent a unicast packet...

            # TODO send txDone up; need a more general way
            if (
                    (isACKed is True)
                    and
                    (self.pktToSend[u'type'] == d.PKT_TYPE_SIXP)
                ):
                self.mote.sixp.recv_mac_ack(self.pktToSend)

            if active_cell:
                self.mote.rpl.indicate_tx(
                    active_cell,
                    self.pktToSend[u'mac'][u'dstMac'],
                    isACKed
                )

                # update the backoff exponent
                self._update_backoff_state(
                    isRetransmission = self._is_retransmission(self.pktToSend),
                    isSharedLink     = d.CELLOPTION_SHARED in active_cell.options,
                    isTXSuccess      = isACKed,
                    packet           = self.pktToSend
                )

            if isACKed:
                # ... which was ACKed

                # As ACK is not represented by a packet, we force the Neighbors Propositions reception expected to be
                # coupled with the ACK (so propositions come from the mote that ACKed the packet)
                self.NPtable.feed_from_ACK(self.pktToSend)

                # update schedule stats
                if active_cell:
                    active_cell.increment_num_tx_ack()

                # time correction
                if self.clock.source == self.pktToSend[u'mac'][u'dstMac']:
                    self.asnLastSync = asn # ACK-based sync
                    self.clock.sync()
                    self._reset_keep_alive_timer()
                    self._reset_synchronization_timer()

                # remove packet from queue
                self.dequeue(self.pktToSend)

                # process the pending bit field
                if (
                        (self.pktToSend[u'mac'][u'pending_bit'] is True)
                        and
                        self._is_next_slot_unused()
                    ):
                    self._schedule_next_tx_for_pending_bit(
                        self.pktToSend[u'mac'][u'dstMac'],
                        channel
                    )
                else:
                    self.args_for_next_pending_bit_task = None

            else:
                # ... which was NOT ACKed

                # decrement 'retriesLeft' counter associated with that packet
                assert self.pktToSend[u'mac'][u'retriesLeft'] >= 0
                self.pktToSend[u'mac'][u'retriesLeft'] -= 1

                # drop packet if retried too many time
                if self.pktToSend[u'mac'][u'retriesLeft'] < 0:

                    # remove packet from queue
                    self.dequeue(self.pktToSend)

                    # drop
                    self.mote.drop_packet(
                        packet = self.pktToSend,
                        reason = SimEngine.SimLog.DROPREASON_MAX_RETRIES,
                    )

        # notify upper layers
        if active_cell:
            assert active_cell.is_tx_on()
            self.mote.sf.indication_tx_cell_elapsed(
                cell        = active_cell,
                sent_packet = self.pktToSend
            )

        # end of radio activity, not waiting for anything
        self.waitingFor = None
        self.pktToSend  = None

    def rxDone(self, packet, channel):

        # local variables
        asn         = self.engine.getAsn()
        active_cell = self.active_cell

        self.active_cell = None

        # copy the received packet to a new packet instance since the passed
        # "packet" should be kept as it is so that Connectivity can use it
        # after this rxDone() process.
        new_packet = copy.deepcopy(packet)
        packet = new_packet

        # make sure I'm in the right state
        assert self.waitingFor == d.WAITING_FOR_RX

        # not waiting for anything anymore
        self.waitingFor = None

        if packet:
            # add the source mote to the neighbor list if it's not listed yet
            if packet[u'mac'][u'srcMac'] not in self.neighbor_table:
                self.neighbor_table.append(packet[u'mac'][u'srcMac'])

            # accept only EBs while we're not syncrhonized
            if (
                    (self.getIsSync() is False)
                    and
                    (not (packet[u'type'] in [d.PKT_TYPE_EB, d.PKT_TYPE_NPEB]))
                ):
                return False # isACKed

            # abort if I received a frame for someone else
            if (
                    (packet[u'mac'][u'dstMac'] != d.BROADCAST_ADDRESS)
                    and
                    (self.mote.is_my_mac_addr(packet[u'mac'][u'dstMac']) is False)
                ):
                return False # isACKed

            # if I get here, I received a frame at the link layer (either unicast for me, or broadcast)

            # log
            self.log(
                SimEngine.SimLog.LOG_TSCH_RXDONE,
                {
                    u'_mote_id':       self.mote.id,
                    u'channel':        channel,
                    u'slot_offset':    (
                        active_cell.slot_offset
                        if active_cell else None
                    ),
                    u'channel_offset': (
                        active_cell.channel_offset
                        if active_cell else None
                    ),
                    u'packet':         packet,
                }
            )

            # time correction
            if self.clock.source == packet[u'mac'][u'srcMac']:
                self.asnLastSync = asn # packet-based sync
                self.clock.sync()
                self._reset_keep_alive_timer()
                self._reset_synchronization_timer()

            # update schedule stats
            if (
                    self.getIsSync()
                    and
                    active_cell
                ):
                    active_cell.increment_num_rx()

            if   self.mote.is_my_mac_addr(packet[u'mac'][u'dstMac']):
                # link-layer unicast to me

                # ACK frame
                isACKed = True

                # save the pending bit here since the packet instance may be made
                # empty by an upper layer process
                is_pending_bit_on = packet[u'mac'][u'pending_bit']

                # dispatch to the right upper layer
                if   packet[u'type'] == d.PKT_TYPE_SIXP:
                    self.mote.sixp.recv_packet(packet)
                elif packet[u'type'] == d.PKT_TYPE_KEEP_ALIVE:
                    # do nothing but send back an ACK
                    pass
                elif u'net' in packet:
                    self.mote.sixlowpan.recvPacket(packet)
                else:
                    raise SystemError()

                if (
                        is_pending_bit_on
                        and
                        self._is_next_slot_unused()
                    ):
                    self._schedule_next_rx_by_pending_bit(channel)

            elif packet[u'mac'][u'dstMac'] == d.BROADCAST_ADDRESS:
                # link-layer broadcast

                # do NOT ACK frame (broadcast)
                isACKed = False

                # dispatch to the right upper layer
                if   packet[u'type'] == d.PKT_TYPE_EB:
                    self._action_receiveEB(packet)
                elif packet[u'type'] == d.PKT_TYPE_NPEB:
                    self._action_receiveNPEB(packet)
                elif u'net' in packet:
                    assert packet[u'type'] in [
                        d.PKT_TYPE_DIO,
                        d.PKT_TYPE_DIS
                    ]
                    self.mote.sixlowpan.recvPacket(packet)
                else:
                    raise SystemError()

            else:
                raise SystemError()
        else:
            # received nothing (idle listen)
            isACKed = False

        # notify upper layers
        if active_cell:
            assert active_cell.is_rx_on()
            self.mote.sf.indication_rx_cell_elapsed(
                cell            = active_cell,
                received_packet = packet
            )

        return isACKed

    #======================== private ==========================================

    # listeningForEB

    def _log_radio_stats(self):
        self.log(
            SimEngine.SimLog.LOG_CHARGE_AFTER_SENDING_EB,
            {
                u'_mote_id': self.mote.id,
                u'idle_listen': self.mote.radio.stats[u'idle_listen'],
                u'tx_data_rx_ack': self.mote.radio.stats[u'tx_data_rx_ack'],
                u'tx_data': self.mote.radio.stats[u'tx_data'],
                u'rx_data_tx_ack': self.mote.radio.stats[u'rx_data_tx_ack'],
                u'rx_data': self.mote.radio.stats[u'rx_data'],
                u'sleep': self.mote.radio.stats[u'sleep']
            }
        )

    def _action_listeningForEB_cell(self):
        """
        active slot starts, while mote is listening for EBs
        """

        assert not self.getIsSync()

        # this event was scheduled 1 slot ago (active listening), take into account elapsed time
        ts_duration_ms = self.settings.tsch_slotDuration
        self.current_EB_delay -= ts_duration_ms * 1000
        if self.current_EB_delay < ts_duration_ms:
            # avoid scheduling event expected at timer expiration in the current timeslot
            self.current_EB_delay = ts_duration_ms

        # choose random channel
        channel = random.choice(self.hopping_sequence)

        # start listening
        self.mote.radio.startRx(channel)

        # indicate that we're waiting for the RX operation to finish
        self.waitingFor = d.WAITING_FOR_RX

        # schedule next listeningForEB cell
        self.schedule_next_listeningForEB_cell()

    def _action_listeningForNPEB_cell(self):
        """
        active slot starts, while mote is listening for an expected NPEB on the retained channel set when this
        event has been scheduled
        """

        assert not self.getIsSync()
        assert self.channel_offset_next_NPEB is not None
        print self.engine.getAsn(), "- Mote", self.mote.id, " wakes up to listen NPEB from determined neighbor at cell", self.engine.getAsn() % self.get_slotframe(0).length, ",", self.channel_offset_next_NPEB
        # start listening
        channel_NPEB = self._get_physical_channel_from_offset(self.channel_offset_next_NPEB)
        self.mote.radio.startRx(channel_NPEB)

        # indicate that we're waiting for the RX operation to finish
        self.waitingFor = d.WAITING_FOR_RX

        # schedule next listeningForEB cell to carry on listening and synchro in case expected NPEB not captured
        # (this event will be removed if an NPEB is captured)
        self.schedule_next_listeningForEB_cell()

    def _perform_synchronization(self, clock_source_mac_addr):
        clock_source = self.engine.get_mote_by_mac_addr(clock_source_mac_addr)
        if clock_source.dagRoot or clock_source.tsch.getIsSync():
            self.clock.sync(clock_source_mac_addr)
            self.setIsSync(True) # mote

            # the mote that sent the EB is now by join proxy
            self.join_proxy = netaddr.EUI(clock_source_mac_addr)

            # add the minimal cell to the schedule (read from EB)
            self.add_minimal_cell() # mote

            # trigger join process
            self.mote.secjoin.startJoinProcess()
        else:
            # our clock source is desynchronized; we cannot get
            # synchronized with the network using the source
            pass

        # clear the EB list
        self.received_eb_list = {}

    def _perform_synchronization_bestEB(self):
        if not self.received_eb_list:
            # this method call should be in a timer task and we should
            # have already been synchronized at the same ASN
            assert self.isSync
            return

        # [Section 6.3.6, IEEE802.15.4-2015]
        # The higher layer may wait for additional
        # MLME-BEACON-NOTIFY.indication primitives before selecting a
        # TSCH network based upon the value of the Join Metric field
        # in the TSCH Synchronization IE. (snip)
        #
        # NOTE- lower value in the Join Metric field indicates that
        # connection of the beaconing device to a specific network
        # device determined by the higher layer is a shorter route.
        clock_source_mac_addr = min(
            self.received_eb_list,
            key=lambda x: self.received_eb_list[x][u'mac'][u'join_metric']
        )
        print self.engine.getAsn(), "- Mote", self.mote.id, "performs synchro considering all EBs jm, selected", clock_source_mac_addr
        self._perform_synchronization(clock_source_mac_addr)

    def _perform_synchronization_bestNP(self):
        assert self.NPtable.bestNP
        print self.engine.getAsn(), "- Mote", self.mote.id, "performs synchro considering best NP :", self.NPtable.bestNP
        self._perform_synchronization(self.NPtable.bestNP)

    def _action_decrease_cycles_NPEB(self):
        # Remove NPEB cells added in slotframe for previous cycle
        self.scheduleNPEB.remove_NPEB_cells_from_SF()
        # Decrease current cycles assigned to NPEB cells to schedule, as we start a new slotframe iteration
        self.scheduleNPEB.cycle_elapsed()
        # Decrease current cycles related to neighbors stored to remain consistent
        self.NPtable.cycle_elapsed()
        # Reschedule to the end of this slotframe iteration
        self.schedule_next_decr_cycles_NPEB()

    # active cell

    def _select_active_cell(self, candidate_cells):
        active_cell = None
        packet_to_send = None

        for cell in candidate_cells:
            if cell.is_tx_on():
                if (
                        (packet_to_send is None)
                        or
                        (
                            self.get_num_packet_in_tx_queue(packet_to_send[u'mac'][u'dstMac'])
                            <
                            self.get_num_packet_in_tx_queue(cell.mac_addr)
                        )
                    ):
                    # try to find a packet to send
                    _packet_to_send = self.get_first_packet_to_send(cell)

                    # take care of the retransmission backoff algorithm
                    if _packet_to_send is not None:
                        if _packet_to_send[u'type'] in [d.PKT_TYPE_EB, d.PKT_TYPE_NPEB]:
                            if (
                                    (
                                        (cell.mac_addr is None)
                                        or
                                        (cell.mac_addr == d.BROADCAST_ADDRESS)
                                    )
                                    and
                                    (
                                        cell.link_type in
                                        [
                                            d.LINKTYPE_ADVERTISING,
                                            d.LINKTYPE_ADVERTISING_ONLY
                                        ]
                                    )
                                ):
                                # we can send the EB on this link (cell)
                                packet_to_send = _packet_to_send
                                active_cell = cell
                            else:
                                # we don't send an EB on a NORMAL
                                # link; skip this one
                                pass
                        elif (
                            cell.is_shared_on()
                            and
                            self._is_retransmission(_packet_to_send)
                            and
                            (u'backoff_remaining_delay' in _packet_to_send)
                            and
                            (_packet_to_send[u'backoff_remaining_delay'] > 0)
                        ):
                            _packet_to_send[u'backoff_remaining_delay'] -= 1
                            # skip this cell for transmission
                        else:
                            packet_to_send = _packet_to_send
                            active_cell = cell

            if (
                    cell.is_rx_on()
                    and
                    (packet_to_send is None)
                ):
                active_cell = cell

        if (
                (packet_to_send is not None)
                and
                (u'backoff_remaining_delay' in packet_to_send)
            ):
            del packet_to_send[u'backoff_remaining_delay']
        return active_cell, packet_to_send

    def _schedule_next_active_slot(self):

        assert self.getIsSync()

        asn       = self.engine.getAsn()
        tsCurrent = asn % self.settings.tsch_slotframeLength

        # find closest active slot in schedule

        if not self.isSync:
            self.engine.removeFutureEvent(uniqueTag=(self.mote.id, u'_action_active_cell'))
            return

        try:
            tsDiffMin = min(
                [
                    slotframe.get_num_slots_to_next_active_cell(asn)
                    for _, slotframe in list(self.slotframes.items()) if (
                        len(slotframe.get_busy_slots()) > 0
                    )
                ]
            )
        except ValueError:
            # we don't have any cell; return without scheduling the next active
            # slot
            return

        # schedule at that ASN
        self.engine.scheduleAtAsn(
            asn            = asn+tsDiffMin,
            cb             = self._action_active_cell,
            uniqueTag      = (self.mote.id, u'_action_active_cell'),
            intraSlotOrder = d.INTRASLOTORDER_STARTSLOT,
        )

    def _action_active_cell(self):
        # cancel a task for the pending bit if scheduled on the same slot
        self.args_for_next_pending_bit_task = None

        # local shorthands
        asn = self.engine.getAsn()

        # make sure we're not in the middle of a TX/RX operation
        assert self.waitingFor == None
        # make sure we are not busy sending a packet
        assert self.pktToSend == None

        # section 6.2.6.4 of IEEE 802.15.4-2015:
        # "When, for any given timeslot, a device has links in multiple
        # slotframes, transmissions take precedence over receives, and lower
        # macSlotframeHandle slotframes takes precedence over higher
        # macSlotframeHandle slotframes."

        candidate_cells = []
        for _, slotframe in list(self.slotframes.items()):
            candidate_cells = slotframe.get_cells_at_asn(asn)
            if len(candidate_cells) > 0:
                break

        if len(candidate_cells) == 0:
            # we don't have any cell at this asn. we may have used to have
            # some, which possibly were removed; do nothing
            pass
        else:
            # identify a cell to be activated
            self.active_cell, self.pktToSend = self._select_active_cell(candidate_cells)

        if self.active_cell:
            if self.pktToSend is None:
                assert self.active_cell.is_rx_on()
                self._action_RX()
            else:
                assert self.active_cell.is_tx_on()
                self._action_TX(
                    pktToSend = self.pktToSend,
                    channel   = self._get_physical_channel(self.active_cell)
                )
                # update cell stats
                self.active_cell.increment_num_tx()
                if self.pktToSend[u'mac'][u'dstMac'] == self.clock.source:
                    # we're going to send a frame to our time source; reset the
                    # keep-alive timer
                    self._reset_keep_alive_timer()
        else:
            # do nothing
            pass

        # notify upper layers
        for cell in candidate_cells:
            # call methods against unselected (non-active) cells
            if cell != self.active_cell:
                if cell.is_tx_on():
                    self.mote.sf.indication_tx_cell_elapsed(
                        cell        = cell,
                        sent_packet = None
                    )
                if cell.is_rx_on():
                    self.mote.sf.indication_rx_cell_elapsed(
                        cell            = cell,
                        received_packet = None
                    )
        # schedule the next active slot
        self._schedule_next_active_slot()

    def _action_TX(self, pktToSend, channel):
        # set the pending bit field
        if (
                (pktToSend[u'mac'][u'dstMac'] != d.BROADCAST_ADDRESS)
                and
                (
                    # we have more than one packet destined to the same
                    # neighbor
                    len(
                        [
                            packet for packet in self.txQueue
                            if (
                                packet[u'mac'][u'dstMac'] ==
                                pktToSend[u'mac'][u'dstMac']
                            )
                        ]
                    ) > 1
                )
                and
                self._is_next_slot_unused()
                and
                self.pending_bit_enabled
            ):
            pktToSend[u'mac'][u'pending_bit'] = True
        else:
            pktToSend[u'mac'][u'pending_bit'] = False

        # send packet to the radio
        self.mote.radio.startTx(channel, pktToSend)

        # indicate that we're waiting for the TX operation to finish
        self.waitingFor = d.WAITING_FOR_TX

    def _action_RX(self):

        # start listening
        self.mote.radio.startRx(
            channel = self._get_physical_channel(self.active_cell)
        )

        # indicate that we're waiting for the RX operation to finish
        self.waitingFor = d.WAITING_FOR_RX

    def _get_physical_channel(self, cell):
        return self._get_physical_channel_from_offset(cell.channel_offset)

    def _get_physical_channel_from_offset(self, channel_offset):
        # see section 6.2.6.3 of IEEE 802.15.4-2015
        return self.hopping_sequence[
            (self.engine.getAsn() + channel_offset) %
            len(self.hopping_sequence)
        ]

    # EBs

    def _decided_to_send_eb(self):
        # short-hand
        prob = float(self.settings.tsch_probBcast_ebProb)
        n    = 1 + len(self.neighbor_table)

        # following the Bayesian broadcasting algorithm
        return (
            (random.random() < (old_div(prob, n)))
            and
            self.iAmSendingEBs
        )

    def _create_EB(self):

        join_metric = self.mote.rpl.getDagRank()
        if join_metric is None:
            newEB = None
        else:
            # create
            newEB = {
                u'type':            d.PKT_TYPE_EB,
                u'mac': {
                    u'srcMac':      self.mote.get_mac_addr(),
                    u'dstMac':      d.BROADCAST_ADDRESS,     # broadcast
                    u'join_metric': self.mote.rpl.getDagRank() - 1
                }
            }

            # log
            self.log(
                SimEngine.SimLog.LOG_TSCH_EB_TX,
                {
                    u'_mote_id': self.mote.id,
                    u'packet':   newEB,
                }
            )

        return newEB

    def _create_NPEB(self):

        join_metric = self.mote.rpl.getDagRank()
        if join_metric is None:  # not already joined the topology
            newNPEB = None
        else:
            # create
            newNPEB = {
                u'type':            d.PKT_TYPE_NPEB,
                u'mac': {
                    u'srcMac':      self.mote.get_mac_addr(),
                    u'dstMac':      d.BROADCAST_ADDRESS,     # broadcast
                    u'join_metric': self.mote.rpl.getDagRank() - 1,
                    u'selfNPEB':    self.scheduleNPEB.get_as_NPEB_field(),
                    u'neighbors':   self.NPtable.select_NPs_to_announce().items()
                    #  \_> list [(mac_neighbor, {join_metric_neigh: ..., scheduleNPEB:
                    #                                                    {cell:(slot_offset, chann_offset),
                    #                                                     curr_cycle: int, nbr_cycles: val}}),
                    #            (mac_neighbor2, {...}) ]
                }
            }

            # log
            self.log(
                SimEngine.SimLog.LOG_TSCH_NPEB_TX,
                {
                    u'_mote_id': self.mote.id,
                    u'packet':   newNPEB,
                }
            )
        print self.engine.getAsn(), "- Mote", self.mote.id, "crafted new NPEB (ASN", self.engine.getAsn(), ") :", newNPEB
        return newNPEB

    def _action_receiveEB(self, packet):

        assert packet[u'type'] == d.PKT_TYPE_EB

        # log
        self.log(
            SimEngine.SimLog.LOG_TSCH_EB_RX,
            {
                u'_mote_id': self.mote.id,
                u'packet':   packet,
            }
        )

        # abort if I'm the root
        if self.mote.dagRoot:
            return

        if not self.getIsSync():
            event_tag = (self.mote.id, u'tsch', u'wait_eb')
            if not self.received_eb_list:
                # start the timer to wait for other EBs if this is the
                # first received EB
                self.engine.scheduleIn(
                    delay          = d.TSCH_MAX_EB_DELAY,
                    cb             = self._perform_synchronization_bestEB,
                    uniqueTag      = event_tag,
                    intraSlotOrder = d.INTRASLOTORDER_STACKTASKS
                )
            # add the EB to the list. If there is an EB from the
            # the source, the EB is replaced by the new one
            self.received_eb_list[packet[u'mac'][u'srcMac']] = packet
            # receiving EB while not sync'ed
            if len(self.received_eb_list) == NPEB_MAX_NEIGHBORS_TO_LISTEN:
                self._perform_synchronization_bestEB()
                self.engine.removeFutureEvent(event_tag)
            else:
                assert len(self.received_eb_list) < NPEB_MAX_NEIGHBORS_TO_LISTEN

    def _action_receiveNPEB(self, packet):

        assert packet[u'type'] == d.PKT_TYPE_NPEB

        # log
        self.log(
            SimEngine.SimLog.LOG_TSCH_NPEB_RX,
            {
                u'_mote_id': self.mote.id,
                u'packet':   packet,
            }
        )

        print self.engine.getAsn(), "- Mote", self.mote.id, " received NPEB", packet
        # feed NPEB table even if already synced or root to possibly learn and announce more neighbors in future NPEBs
        self.NPtable.feed_from_NPEB(packet)

        # abort if I'm the root
        if self.mote.dagRoot:
            return

        if not self.getIsSync():
            event_tag = (self.mote.id, u'tsch', u'wait_eb')
            mac_sender = packet[u'mac'][u'srcMac']

            if self.NPtable.bestNP is None:
                self.NPtable.set_bestNP(mac_sender)
            else:
                # Maybe the neighbor we received the NPEB from is better (should take in account signal)
                self.NPtable.set_bestNP_if_better(mac_sender)

            self.received_eb_list[mac_sender] = packet
            if len(self.received_eb_list) == NPEB_MAX_NEIGHBORS_TO_LISTEN:
                print self.engine.getAsn(), "- Mote", self.mote.id, "has heard enough (NP)EBs and undergoes synchro"
                self._perform_synchronization_bestEB()
                self.engine.removeFutureEvent(event_tag)
                return

            if self.should_undergo_synchro_with_bestNP():
                print self.engine.getAsn(), "- Mote", self.mote.id, " decided to undergo synchro with its bestNP ", self.NPtable.bestNP, " :", self.NPtable.get_bestNP_entry()
                self.engine.removeFutureEvent(event_tag)
                self.engine.removeFutureEvent((self.mote.id, u'_action_listeningForEB_cell'))
                self._perform_synchronization_bestNP()
                return

            # As we fed table with new neighbors infos from the NPEB, maybe one is interesting we should give
            # a try listening the NPEB he plan to emit in the future
            next_neighbor_to_listen, scheduleNPEB = self.NPtable.next_interesting_NPEB()

            if next_neighbor_to_listen is not None:
                # sleep until the NPEB announcement cell by this interesting neighbor, cancel timer EB delay
                print self.engine.getAsn(), "- Mote", self.mote.id, " found interesting NPEB entry to listen", next_neighbor_to_listen, "scheduleNPEB", scheduleNPEB
                self.engine.removeFutureEvent(event_tag)
                self.engine.removeFutureEvent((self.mote.id, u'_action_listeningForEB_cell'))
                # mark that we will listen to this neighbor to keep a trace of neighbors listened
                self.NPtable.mark_neighbor_as_listened(next_neighbor_to_listen)
                # schedule event to wake up and listen for this NPEB in likely multiple cycles
                self.schedule_next_listeningForNPEB_cell(scheduleNPEB)
            else:
                # no interesting neighbor in the NPEB, wait for other EBs randomly (the event
                # _action_listeningForEB_cell is not removed
                print self.engine.getAsn(), "- Mote", self.mote.id, " didnt find interesting neighbor, wait other EBs in the delay", self.current_EB_delay, "seconds"
                self.engine.scheduleIn(
                    delay=self.current_EB_delay,
                    cb=self._perform_synchronization_bestEB,
                    uniqueTag=event_tag,
                    intraSlotOrder=d.INTRASLOTORDER_STACKTASKS
                )

    # Retransmission backoff algorithm
    def _is_retransmission(self, packet):
        assert packet is not None
        if u'retriesLeft' not in packet[u'mac']:
            assert packet[u'mac'][u'dstMac'] == d.BROADCAST_ADDRESS
            return False
        else:
            return (
                packet[u'mac'][u'retriesLeft'] < self.max_tx_retries
            )

    def _decide_backoff_delay(self):
        # Section 6.2.5.3 of IEEE 802.15.4-2015: "The MAC sublayer shall delay
        # for a random number in the range 0 to (2**BE - 1) shared links (on
        # any slotframe) before attempting a retransmission on a shared link."
        return random.randint(0, pow(2, self.backoff_exponent) - 1)

    def _reset_backoff_state(self):
        old_be = self.backoff_exponent
        self.backoff_exponent = d.TSCH_MIN_BACKOFF_EXPONENT
        self.log(
            SimEngine.SimLog.LOG_TSCH_BACKOFF_EXPONENT_UPDATED,
            {
                u'_mote_id': self.mote.id,
                u'old_be'  : old_be,
                u'new_be'  : self.backoff_exponent
            }
        )

    def _increase_backoff_exponent(self):
        old_be = self.backoff_exponent
        # In Figure 6-6 of IEEE 802.15.4, BE (backoff exponent) is updated as
        # "BE - min(BE 0 1, macMinBe)". However, it must be incorrect. The
        # right formula should be "BE = min(BE + 1, macMaxBe)", that we apply
        # here.
        self.backoff_exponent = min(
            self.backoff_exponent + 1,
            d.TSCH_MAX_BACKOFF_EXPONENT
        )
        self.log(
            SimEngine.SimLog.LOG_TSCH_BACKOFF_EXPONENT_UPDATED,
            {
                u'_mote_id': self.mote.id,
                u'old_be'  : old_be,
                u'new_be'  : self.backoff_exponent
            }
        )

    def _update_backoff_state(
            self,
            isRetransmission,
            isSharedLink,
            isTXSuccess,
            packet
        ):
        if isSharedLink:
            if isTXSuccess:
                # Section 6.2.5.3 of IEEE 802.15.4-2015: "A successful
                # transmission in a shared link resets the backoff window to
                # the minimum value."
                self._reset_backoff_state()
            else:
                if isRetransmission:
                    # Section 6.2.5.3 of IEEE 802.15.4-2015: "The backoff window
                    # increases for each consecutive failed transmission in a
                    # shared link."
                    self._increase_backoff_exponent()
                else:
                    # First attempt to transmit the packet
                    #
                    # Section 6.2.5.3 of IEEE 802.15.4-2015: "A device upon
                    # encountering a transmission failure in a shared link
                    # shall initialize the BE to macMinBe."
                    self._reset_backoff_state()
                packet[u'backoff_remaining_delay'] = self._decide_backoff_delay()

        else:
            # dedicated link (which is different from a dedicated *cell*)
            if isTXSuccess:
                # successful transmission
                if len(self.txQueue) == 0:
                    # Section 6.2.5.3 of IEEE 802.15.4-2015: "The backoff
                    # window is reset to the minimum value if the transmission
                    # in a dedicated link is successful and the transmit queue
                    # is then empty."
                    self._reset_backoff_state()
                else:
                    # Section 6.2.5.3 of IEEE 802.15.4-2015: "The backoff
                    # window does not change when a transmission is successful
                    # in a dedicated link and the transmission queue is still
                    # not empty afterwards."
                    pass
            else:
                # Section 6.2.5.3 of IEEE 802.15.4-2015: "The backoff window
                # does not change when a transmission is a failure in a
                # dedicated link."
                pass

    # Synchronization / Keep-Alive
    def _send_keep_alive_message(self):
        if self.clock.source is None:
            return

        if (
                (len(self.txQueue) > 0)
                and
                (self.txQueue[0][u'mac'][u'dstMac'] == self.clock.source)
            ):
            # don't send a keep-alive packet if the first packet in the TX
            # queue has the MAC address of the preferred parent (clock source)
            # as its destination address
            return

        packet = {
            u'type': d.PKT_TYPE_KEEP_ALIVE,
            u'mac': {
                u'srcMac': self.mote.get_mac_addr(),
                u'dstMac': self.clock.source
            }
        }
        self.enqueue(packet, priority=True)
        # the next keep-alive event will be scheduled on receiving an ACK

    def _start_keep_alive_timer(self):
        assert self.settings.tsch_keep_alive_interval >= 0
        if (
                (self.settings.tsch_keep_alive_interval == 0)
                or
                (self.mote.dagRoot is True)
            ):
            # do nothing
            pass
        else:
            # the clock drift of the child against the parent should be less
            # than macTsRxWait/2 so that they can communicate with each
            # other. Their clocks can be off by one clock interval at the
            # most. This means, the clock difference between the child and the
            # parent could be clock_interval just after synchronization. then,
            # the possible minimum guard time is ((macTsRxWait / 2) -
            # clock_interval). When macTsRxWait is 2,200 usec and
            # clock_interval is 30 usec, the minimum guard time is 1,070
            # usec. they will be desynchronized without keep-alive in 16
            # seconds as the paper titled "Adaptive Synchronization in
            # IEEE802.15.4e Networks" describes.
            #
            # the keep-alive interval should be configured in config.json with
            # "tsch_keep_alive_interval".
            self.engine.scheduleIn(
                delay          = self.settings.tsch_keep_alive_interval,
                cb             = self._send_keep_alive_message,
                uniqueTag      = self._get_event_tag(u'tsch.keep_alive_event'),
                intraSlotOrder = d.INTRASLOTORDER_STACKTASKS
            )

    def _stop_keep_alive_timer(self):
        self.engine.removeFutureEvent(
            uniqueTag = self._get_event_tag(u'tsch.keep_alive_event')
        )

    def _reset_keep_alive_timer(self):
        self._stop_keep_alive_timer()
        self._start_keep_alive_timer()

    def _start_synchronization_timer(self):
        self._reset_synchronization_timer()

    def _stop_synchronization_timer(self):
        self.engine.removeFutureEvent(
            uniqueTag = self._get_event_tag(u'tsch.synchronization_timer')
        )

    def _reset_synchronization_timer(self):
        if (
                (self.settings.tsch_keep_alive_interval == 0)
                or
                (self.mote.dagRoot is True)
            ):
            # do nothing
            pass
        else:
            target_asn = self.engine.getAsn() + d.TSCH_DESYNCHRONIZED_TIMEOUT_SLOTS

            def _desync():
                self.setIsSync(False)

            self.engine.scheduleAtAsn(
                asn            = target_asn,
                cb             = _desync,
                uniqueTag      = self._get_event_tag(u'tsch.synchronization_timer'),
                intraSlotOrder = d.INTRASLOTORDER_STACKTASKS
            )

    def _get_event_tag(self, event_name):
        return u'{0}-{1}'.format(self.mote.id, event_name)

    def _get_synchronization_event_tag(self):
        return u'{0}-{1}.format()'

    # Pending bit
    def _schedule_next_tx_for_pending_bit(self, dstMac, channel):
        self.args_for_next_pending_bit_task = {
            u'dstMac' : dstMac,
            u'channel': channel
        }
        self.engine.scheduleAtAsn(
            asn            = self.engine.getAsn() + 1,
            cb             = self._action_tx_for_pending_bit,
            uniqueTag      = (self.mote.id, u'_action_tx_for_pending_bit'),
            intraSlotOrder = d.INTRASLOTORDER_STARTSLOT,
        )

    def _schedule_next_rx_by_pending_bit(self, channel):
        self.args_for_next_pending_bit_task = {
            u'channel': channel
        }
        self.engine.scheduleAtAsn(
            asn            = self.engine.getAsn() + 1,
            cb             = self._action_rx_for_pending_bit,
            uniqueTag      = (self.mote.id, u'_action_rx_for_pending_bit'),
            intraSlotOrder = d.INTRASLOTORDER_STARTSLOT,
        )

    def _action_tx_for_pending_bit(self):
        if self.args_for_next_pending_bit_task is None:
            # it seems this TX was canceled by an active cell scheduled on the
            # same slot
            return

        assert self.waitingFor == None
        assert self.pktToSend == None

        for packet in self.txQueue:
            if (
                    packet[u'mac'][u'dstMac'] ==
                    self.args_for_next_pending_bit_task[u'dstMac']
                ):
                self.pktToSend = packet
                break

        if self.pktToSend is None:
            # done
            return
        else:
            # self.args_for_next_pending_bit_task will be updated in the TX
            # operation
            self._action_TX(
                pktToSend = self.pktToSend,
                channel   = self.args_for_next_pending_bit_task[u'channel']
            )

    def _action_rx_for_pending_bit(self):
        if self.args_for_next_pending_bit_task is None:
            # it seems this RX was canceled by an active cell scheduled on the
            # same slot
            return

        # self.args_for_next_pending_bit_task will be updated in the RX
        # operation
        self.mote.radio.startRx(
            self.args_for_next_pending_bit_task[u'channel']
        )
        self.waitingFor = d.WAITING_FOR_RX

    def _is_next_slot_unused(self):
        ret_val = True
        for slotframe in list(self.slotframes.values()):
            next_slot = (self.engine.getAsn() + 1) % slotframe.length
            cells_on_next_slot = slotframe.get_cells_by_slot_offset(next_slot)
            if len(cells_on_next_slot) > 0:
                ret_val = False
                break

        return ret_val


class scheduleNPEB(object):

    # Maintain coordinates of cells used to emit NPEB and the number of slotframe iterations "cycles" between each.
    # To each cell is related a current cycle curr_cycle and a number of cycles nbr_cycles :
    # at each slotframe iteration we do curr_cycle--, arriving at curr_cycle=0 we install a new cell at corresponding
    # coordinates in the current slotframe that begins, where a NPEB will be sent. At the end of this slotframe
    # iteration curr_cycle is reset at nbr_cycles and the installed cell is removed from the slotframe.

    # TODO : cells should be recomputed when the mote change its place in RPL topology (new cycles values at least)
    # TODO : the number of cells may be adapted dynamically depending number of neighbors

    def __init__(self, tsch):
        self.tsch = tsch
        self.slotframe = self.tsch.get_slotframe(0)
        self.NPEBcells = {}  # indexed by couples (tsOffset, chOffset)
        self.NPEBcells_to_remove = []  # NPEB cells added in slotframe for only the current cycle

    def create_cell(self, slot_offset, channel_offset):
        # create an actual cell for broadcasting NPEB
        cell = Cell(slot_offset, channel_offset, [d.CELLOPTION_TX, d.CELLOPTION_SHARED],
                    link_type=d.LINKTYPE_ADVERTISING_ONLY)
        return cell

    def register_new_cell(self, slot_offset, channel_offset, nbr_cycles, curr_cycle=1):
        # register a new "cell" (given as coordinates) that will be instantiated every nbr_cycles cycles
        assert nbr_cycles > 0

        self.NPEBcells[(slot_offset, channel_offset)] = {u'curr_cycle': curr_cycle,
                                                         u'nbr_cycles': nbr_cycles}
        print self.tsch.engine.getAsn(), "- Mote", self.tsch.mote.id, "registered new NPEB cell, schedule is now ", self.NPEBcells
        self.tsch.log(
            SimEngine.SimLog.LOG_TSCH_REGISTER_NPEB_CELL,
            {
                u'_mote_id': self.tsch.mote.id,
                u'slotOffset': slot_offset,
                u'channelOffset': channel_offset,
                u'nbr_cycles': nbr_cycles
            }
        )

    def get_new_cell_best_offsets(self, after_timeslot=1):
        # what would be best coordinates for a new NPEB cell ? the closest possible to the beginning of the slotframe
        # (to daisy chain NPEB reception -> listening new announced neighbor) but avoiding to use a slot already
        # used by a neighbor for NPEB broadcasting (we know partially this information from the current NPEB table)
        return self.tsch.NPtable.get_first_unoccupied_possible_NPEBcell(after_timeslot=after_timeslot,
                                                                        add_excluded_cells=self.NPEBcells.keys())

    def auto_register_new_cell(self):
        # let try an automatic best decision process to determinate best coordinates and cycle for a new NPEB
        # cell and register it
        nbr_cycles = self.get_best_cycles_nbr()
        best_starting_cycle_offset = self.get_best_cycle_curr_offset(nbr_cycles)
        nbr_already_registered = len(self.NPEBcells)
        if nbr_already_registered == 0:
            after_timeslot = 1  # First cell, closest as possible from start of slotframe
        else:
            # spread along first half of slotframe
            after_timeslot = int(self.slotframe.length / (nbr_already_registered + 1))
        slot_offset, channel_offset = self.get_new_cell_best_offsets(after_timeslot=after_timeslot)
        self.register_new_cell(slot_offset, channel_offset, nbr_cycles, best_starting_cycle_offset)

    def get_best_cycles_nbr(self):
        # computes a number of cycles taking in account the join metric of the mote
        # lower jm -> good place in RPL topology -> should announce NPEBs more often -> shorter interval (nbr_cycles)
        jm = self.tsch.mote.rpl.getDagRank() - 1
        if self.tsch.mote.dagRoot:
            nbr_cycles = NPEB_MIN_NBR_CYCLES
        else:
            nbr_cycles = NPEB_NON_ROOT_MIN_NBR_CYCLES
        nbr_cycles += int(jm / NPEB_JM_THRESH_NBR_CYCLES)
        return min(NPEB_MAX_NBR_CYCLES, nbr_cycles)

    def get_best_cycle_curr_offset(self, nbr_cycles):
        # consider NPtable to see which neighbors announce NPEB every nbr_cycles cycles and their current cycle,
        # return an offset to be shifted and cover more iterations of slotframes
        taken_offsets = []
        for neigh_info in self.tsch.NPtable.NPs.values():
            nbr_cycle_neigh = neigh_info[u'scheduleNPEB'][u'nbr_cycles']
            if nbr_cycle_neigh == nbr_cycles:
                curr_cycle = neigh_info[u'scheduleNPEB'][u'curr_cycle']
                if not(curr_cycle in taken_offsets):
                    taken_offsets.append(curr_cycle)
        for curr_cycle_shifted in range(1, nbr_cycles+1):
            if not(curr_cycle_shifted in taken_offsets):
                return curr_cycle_shifted
        # all possible offsets are taken, let return 1 to be efficient
        return 1

    def is_cell_registered(self, cell):
        return self.NPEBcells.get((cell.slot_offset, cell.channel_offset)) is not None

    def cycle_elapsed(self):
        # decrease curr_cycle for each registered cell and install the actual cell in the slotframe if curr_cycle
        # reaches 0 (removed automatically at the end of the slotframe iteration)
        for cell, cycle_infos in self.NPEBcells.items():
            curr_cycle = cycle_infos[u'curr_cycle']
            assert curr_cycle >= 0
            if curr_cycle == 0:
                cycle_infos[u'curr_cycle'] = cycle_infos[u'nbr_cycles']
            elif curr_cycle == 1:
                cycle_infos[u'curr_cycle'] = 0  # A NPEB announcement cell will be set for this current cycle
                print self.tsch.engine.getAsn(), "- Mote", self.tsch.mote.id, "has a cycle counter arriving to 0 and schedules an NPEB cell", cell
                self.schedule_NPEB_cell_curr_cycle(cell)
            else:
                cycle_infos[u'curr_cycle'] = curr_cycle - 1

    def schedule_NPEB_cell_curr_cycle(self, cell_coord):
        # install a cell in the current slotframe iteration and retain it to be removed at its end
        cell = self.create_cell(cell_coord[0], cell_coord[1])
        self.slotframe.add(cell)  # will be deleted at end of cycle by _action_decrease_cycles_NPEB
        self.NPEBcells_to_remove.append(cell)
        assert cell in self.slotframe.get_cells_by_slot_offset(cell_coord[0])

    def remove_NPEB_cells_from_SF(self):
        # remove all NPEB announcement cells installed in the slotframe
        for cell in self.NPEBcells_to_remove:
            self.slotframe.delete(cell)
        self.NPEBcells_to_remove = []

    def get_as_NPEB_field(self):
        # pick one of the registered cell to be announced in an NPEB sent by this mote
        # picking the farthest in term of remaining cycles allow a node receiving the NPEB to have time to join
        # and when done, announce NPEBs indicating that this node will emit an NPEB soon
        farthest_cell = None
        farthest_cycle = -1
        for cell, cycle_infos in self.NPEBcells.items():
            if cycle_infos[u'curr_cycle'] > farthest_cycle:
                farthest_cycle = cycle_infos[u'curr_cycle']
                farthest_cell = cell
        if farthest_cell is not None:
            curr_cycle, nbr_cycles = farthest_cycle, self.NPEBcells[farthest_cell][u'nbr_cycles']
            return {u'cell': farthest_cell,
                    u'curr_cycle': curr_cycle,
                    u'nbr_cycles': nbr_cycles}

    def clear(self):
        self.NPEBcells = {}
        self.NPEBcells_to_remove = []

    def __iter__(self):
        return self.NPEBcells.__iter__()

    def __getitem__(self, item):
        return self.NPEBcells[item]


class NPtable(object):

    # The Neighbors Propositions table is used to store information about neighbour related to NPEB usage. In a first
    # time when mote is in active search for a neighbor to synchronize on, the table is fed by infos in captured NPEBs
    # and contributes to decide whether there is a potentially interesting neighbor to listen to its NPEB. In a second
    # time (mote joined), the content of the table stands for candidates to propose in NPEBs the mote is now able to
    # emit. The table stores following information indexed by neighbors MAC address :
    #   { mac_neigh1 : { join_metric: val,
    #                    signal: val or None (indicates neighbor learned by NPEB but not yet captured NPEB from it)
    #                            or False (gave a try listening its scheduled NP but captured nothing)
    #                    scheduleNPEB : { cell: (slotOffset, channelOffset), curr_cycle: val, nbr_cycles: val}
    #                   },
    #     mac_neigh2 : { ... } }

    def __init__(self, tsch):
        self.tsch = tsch
        self.NPs = {}  # indexed by nodes MAC
        self.bestNP = None  # best Neighbor Proposition we got an NPEB from for synch process (MAC address)

    def select_NPs(self, slct_score_fct, thresh_score=0, max_nbr=1, list_macs=False):
        # Retrieve ordered and filtered entries from the table, based on a score function applied on each and a
        # threshold. The function slct_score_fct must return tuples (mac_neigh, score_value)
        score_NPs = map(slct_score_fct, self.NPs.items())
        filtered = filter(lambda scored: scored[1] >= thresh_score, score_NPs)
        ordered = sorted(filtered, key=lambda scored: scored[1])
        reduced = ordered[:min(len(ordered), max_nbr)]
        if list_macs:
            return [scored[0] for scored in reduced]
        return {neighbor: self.NPs[neighbor].copy() for neighbor, _ in reduced}

    def cycle_elapsed(self):
        for neigh_infos in self.NPs.values():
            schedule = neigh_infos[u'scheduleNPEB']
            current = schedule[u'curr_cycle']
            assert current >= 0
            if current == 0:
                schedule[u'curr_cycle'] = schedule[u'nbr_cycles']
            else:
                schedule[u'curr_cycle'] = current - 1

    # --- Listening and feeding new NPEB
    def feed(self, neighbor, join_metric, scheduleNPEB, signal_strength=None):
        # Add a new entry in the table or replace current one if already exists for this neighbor (MAC)
        old = self.NPs.get(neighbor)
        if old is not None:
            if not(old[u'signal'] in [None, False]):
                signal_strength = old[u'signal']
        self.NPs[neighbor] = {u'join_metric': join_metric,
                              u'signal': signal_strength,
                              u'scheduleNPEB': scheduleNPEB}

        self.tsch.log(
            SimEngine.SimLog.LOG_TSCH_FEED_NPTABLE,
            {
                u'_mote_id': self.tsch.mote.id,
                u'neighbor': neighbor,
                u'neighbor_id': self.tsch.engine.get_mote_by_mac_addr(neighbor).id,
                u'join_metric': join_metric,
                u'signal': signal_strength,
                u'newScheduleNPEB': scheduleNPEB
            }
        )

    def feed_from_NPEB(self, eb_struct):
        # From a captured NPEB, feed the table with information about neighbors proposed in it and the mote that
        # sent the NPEB (for which we have so the signal strength)
        assert eb_struct[u'type'] == d.PKT_TYPE_NPEB
        assert self.tsch.mote.radio.channel

        # feed neighbor entry for the NPEB sender
        sender_NPEB_infos = eb_struct[u'mac'].get(u'selfNPEB')
        if sender_NPEB_infos is not None:
            src = eb_struct[u'mac'][u'srcMac']
            src_mote_id = self.tsch.engine.get_mote_by_mac_addr(src).id
            jm = eb_struct[u'mac'][u'join_metric']
            signal = self.tsch.engine.connectivity.get_rssi(src_mote_id, self.tsch.mote.id,
                                                            self.tsch.mote.radio.channel)
            self.feed(src, jm, sender_NPEB_infos, signal)

        # feed all additional neighbors entries in the NPEB
        neighbors_NPEB_infos = eb_struct[u'mac'].get(u'neighbors')
        if neighbors_NPEB_infos:
            for mac_neigh, NPEB_infos in neighbors_NPEB_infos:
                jm = NPEB_infos[u'join_metric']
                scheduleNPEB = NPEB_infos[u'scheduleNPEB']
                self.feed(mac_neigh, jm, scheduleNPEB)

    def feed_from_data_pkt(self, data_pkt_struct):
        pass

    def feed_from_ACK(self, ack_struct):
        # ACK_sctruct is actually the packet that was ACKed as there is no dedicated struct in the simulator for ACK
        # TODO : seems to sometimes update inconcistently, only curr_cycle is decremented by one for 1 neighbor
        mote_that_acked = self.tsch.engine.get_mote_by_mac_addr(ack_struct[u'mac'][u'dstMac'])
        ack_NPs = mote_that_acked.tsch.retrieve_NPs_for_ACK(self.tsch.mote.get_mac_addr())
        print self.tsch.engine.getAsn(), "- Mote", self.tsch.mote.id, "try feed from ACK NPs created", ack_NPs, "from packet", ack_struct
        if ack_NPs is None:  # ACKing node not already in topology
            return
        sender_ack_infos = ack_NPs[u'selfNPEB']
        if sender_ack_infos is not None:
            jm = ack_NPs[u'join_metric']
            signal = self.tsch.engine.connectivity.get_rssi(mote_that_acked.id, self.tsch.mote.id,
                                                            self.tsch.mote.radio.channel)
            self.feed(mote_that_acked.get_mac_addr(), jm, sender_ack_infos, signal)
        neighbors_NPEB_infos = ack_NPs[u'neighbors']
        if neighbors_NPEB_infos:
            for mac_neigh, NPEB_infos in neighbors_NPEB_infos:
                if mac_neigh != self.tsch.mote.get_mac_addr():  # Avoid placing itself in NPtable
                    jm = NPEB_infos[u'join_metric']
                    scheduleNPEB = NPEB_infos[u'scheduleNPEB']
                    self.feed(mac_neigh, jm, scheduleNPEB)

    def set_bestNP(self, neighbor_mac):
        print self.tsch.engine.getAsn(), "- Mote", self.tsch.mote.id, " sets its bestNP to ", neighbor_mac
        self.bestNP = neighbor_mac

    def get_bestNP_entry(self):
        # get infos for the neighbor referenced as best until now
        return self.NPs[self.bestNP]

    def set_bestNP_if_better(self, neighbor_candidate_mac):
        def compare_received_NPEB_entries(curr_best, candidate):
            # TODO : may be relaxed ton consider neighbors with close value
            return candidate[u'signal'] > curr_best[u'signal']

        if compare_received_NPEB_entries(self.get_bestNP_entry(), self.NPs[neighbor_candidate_mac]):
            self.set_bestNP(neighbor_candidate_mac)

    def select_NP_to_listen(self):
        # retrieve what seems the best neighbor not listened yet following diverse criteria
        farthest_cycle = self.get_cycles_farthest_announce()

        def score_listen((mac_neigh, infos)):
            if infos[u'signal'] is not None:
                return mac_neigh, -1  # already captured or tried to an EB from this neighbor
            score = 255
            score -= infos[u'join_metric']
            # a closest announcement has a priority for same metric
            # score += farthest_cycle - infos[u'scheduleNPEB'][u'curr_cycle']
            # if infos[u'join_metric'] == 0:  # DAG root
            #     score *= 2
            return mac_neigh, score

        return self.select_NPs(lambda info_neigh: score_listen(info_neigh), list_macs=True)

    def next_interesting_NPEB(self):
        # Look in neighbors table for NPEB possibly more interesting than current bestNP
        def compare_NPEBs_entries(curr_best, candidate):
            # TODO : may be relaxed ton consider neighbors with close value
            return candidate[u'join_metric'] <= curr_best[u'join_metric']

        next_to_listen = self.select_NP_to_listen()
        if next_to_listen:
            next_to_listen = next_to_listen[0]
            if compare_NPEBs_entries(self.NPs[self.bestNP], self.NPs[next_to_listen]):
                # candidate seems better, should listen to its NPEB in the future
                return next_to_listen, self.NPs[next_to_listen][u'scheduleNPEB']
        # No interesting neighbour announcing NPEB in comparison with the current best one
        return None, {}

    def mark_neighbor_as_listened(self, mac_neigh):
        assert mac_neigh in self.NPs
        self.NPs[mac_neigh][u'signal'] = False

    def is_still_neighbor_to_listen(self):
        for neigh_infos in self.NPs.values():
            if neigh_infos[u'signal'] is None:
                return True

    # --- Announcing NPEB to neighbors
    def select_NPs_to_announce(self):
        # retrieve what seems to be the best known neighbors to announce in a NPEB
        farthest_cycle = self.get_cycles_farthest_announce()

        def score_announce((mac_neigh, infos)):
            score = 255
            score -= infos[u'join_metric']
            # a closest announcement has a priority for same metric
            # score += farthest_cycle - infos[u'scheduleNPEB'][u'curr_cycle']
            if mac_neigh == self.tsch.mote.rpl.getPreferredParent(): #or infos[u'join_metric'] == 0:
                score *= 2
            return mac_neigh, score

        neighbors_for_NPEB = self.select_NPs(score_announce, self.get_nbr_neighbors_NPEB())
        for infos in neighbors_for_NPEB.values():
            del infos[u'signal']  # not relevant for the receiver of NPEB
        return neighbors_for_NPEB

    # --- Others
    def clear(self):
        self.NPs = {}
        self.bestNP = None

    def clean_unreceived_NPEB(self):
        clean = {}
        for neighbor, infos in self.NPs.items():
            if infos.get(u'signal') is not False:
                clean[neighbor] = infos
        self.NPs = clean

    def get_nbr_neighbors_NPEB(self):
        return NPEB_MAX_NEIGHBORS_ANNOUNCED

    def get_occupied_NPEBcells(self):
        # list all cells used by neighbors to announce their NPEB
        occupied = []
        for neigh_infos in self.NPs.values():
            occupied.append(neigh_infos[u'scheduleNPEB'][u'cell'])
        return occupied

    def get_first_unoccupied_possible_NPEBcell(self, after_timeslot=1, add_excluded_cells=[]):
        # considering busy slots by itself and neighbors, returns first free cell where no NPEB is announced
        lenSF0 = self.tsch.get_slotframe(0).length
        assert after_timeslot < lenSF0

        try:
            getattr(self.tsch.mote.sf, "_compute_autonomous_cell", None)
            mote_mac = self.tsch.mote.get_mac_addr()
            reserved_cell = self.tsch.mote.sf._compute_autonomous_cell(mote_mac)
            add_excluded_cells.append(reserved_cell)
        except (AttributeError, TypeError):
            pass
        occupied = self.get_occupied_NPEBcells()
        used_ts_SF0 = self.tsch.get_busy_slots()
        excluded_cells = occupied + add_excluded_cells
        all_used_ts = used_ts_SF0 + [ts for ts, _ in excluded_cells]
        for ts_offset in range(after_timeslot, lenSF0):  # Exclude first slot
            if ts_offset in all_used_ts:
                continue  # already used by this node itself
            used_channels = range(0, self.tsch.settings.phy_numChans)
            if RDM_CHANNEL_NEW_NPEB_CELL:
                used_ch_for_ts = [ch for ts, ch in excluded_cells if ts == ts_offset]
                available_ch = list(set(used_channels) - set(used_ch_for_ts))
                if not available_ch:
                    return ts_offset, random.choice(used_channels)
                else:
                    return ts_offset, random.choice(available_ch)
            for ch_offset in used_channels:
                if not((ts_offset, ch_offset) in occupied + add_excluded_cells):
                    return ts_offset, ch_offset

    def get_cycles_farthest_announce(self):
        farthest = -1
        for neigh_infos in self.NPs.values():
            farthest = max(neigh_infos[u'scheduleNPEB'][u'curr_cycle'], farthest)
        return None if farthest == -1 else farthest

    def __len__(self):
        return len(self.NPs)

    def __iter__(self):
        return self.NPs.__iter__()

    def __getitem__(self, item):
        return self.NPs[item]


class Clock(object):
    def __init__(self, mote):
        # singleton
        self.engine   = SimEngine.SimEngine.SimEngine()
        self.settings = SimEngine.SimSettings.SimSettings()

        # local variables
        self.mote = mote

        # instance variables which can be accessed directly from outside
        self.source = None

        # private variables
        self._clock_interval = 1.0 / self.settings.tsch_clock_frequency
        self._error_rate     = self._initialize_error_rate()

        self.desync()

    @staticmethod
    def get_clock_by_mac_addr(mac_addr):
        engine = SimEngine.SimEngine.SimEngine()
        mote = engine.get_mote_by_mac_addr(mac_addr)
        return mote.tsch.clock

    def desync(self):
        self.source             = None
        self._clock_off_on_sync = 0
        self._accumulated_error = 0
        self._last_clock_access = None

    def sync(self, clock_source=None):
        if self.mote.dagRoot is True:
            # if you're the DAGRoot, you should have the perfect clock from the
            # point of view of the network.
            self._clock_off_on_sync = 0
        else:
            if clock_source is None:
                assert self.source is not None
            else:
                self.source = clock_source

            # the clock could be off by between 0 and 30 usec (clock interval)
            # from the clock source when 32.768 Hz oscillators are used on the
            # both sides. in addition, the clock source also off from a certain
            # amount of time from its source.
            off_from_source = random.random() * self._clock_interval
            source_clock = self.get_clock_by_mac_addr(self.source)
            self._clock_off_on_sync = off_from_source + source_clock.get_drift()

        self._accumulated_error = 0
        self._last_clock_access = self.engine.getAsn()

    def get_drift(self):
        if self.mote.dagRoot is True:
            # if we're the DAGRoot, we are the clock source of the entire
            # network. our clock never drifts from itself. Its clock drift is
            # taken into accout by motes who use our clock as their reference
            # clock.
            error = 0
        elif self._last_clock_access:
            assert self._last_clock_access <= self.engine.getAsn()
            slot_duration = self.engine.settings.tsch_slotDuration
            elapsed_slots = self.engine.getAsn() - self._last_clock_access
            elapsed_time  = elapsed_slots * slot_duration
            error = elapsed_time * self._error_rate
        else:
            # self._last_clock_access is None; we're desynchronized.
            # in this case, we will return 0 as drift, although there
            # should be a better thing to do.
            error = None

        if error:
            # update the variables
            self._accumulated_error += error
            self._last_clock_access = self.engine.getAsn()

            # return the result
            return self._clock_off_on_sync + self._accumulated_error
        else:
            return 0

    def _initialize_error_rate(self):
        # private variables:
        # the clock drifts by its error rate. for simplicity, we double the
        # error rate to express clock drift from the time source. That is,
        # our clock could drift by 30 ppm at the most and the clock of time
        # source also could drift as well ppm. Then, our clock could drift
        # by 60 ppm from the clock of the time source.
        #
        # we assume the error rate is constant over the simulation time.
        max_drift = (
            float(self.settings.tsch_clock_max_drift_ppm) / pow(10, 6)
        )
        return random.uniform(-1 * max_drift * 2, max_drift * 2)


class SlotFrame(object):
    def __init__(self, mote_id, slotframe_handle, num_slots):
        self.log = SimEngine.SimLog.SimLog().log

        self.mote_id = mote_id
        self.slotframe_handle = slotframe_handle
        self.length = num_slots
        self.slots  = {}
        # index by neighbor_mac_addr for quick access
        self.cells  = {}

    def __repr__(self):
        return u'slotframe(length: {0}, num_cells: {1})'.format(
            self.length,
            len(list(chain.from_iterable(list(self.slots.values()))))
        )

    def add(self, cell):
        assert cell.slot_offset < self.length
        if cell.slot_offset not in self.slots:
            self.slots[cell.slot_offset] = [cell]
        else:
            self.slots[cell.slot_offset] += [cell]

        if cell.mac_addr not in self.cells:
            self.cells[cell.mac_addr] = [cell]
        else:
            self.cells[cell.mac_addr] += [cell]
        cell.slotframe = self

        # log
        self.log(
            SimEngine.SimLog.LOG_TSCH_ADD_CELL,
            {
                u'_mote_id':        self.mote_id,
                u'slotFrameHandle': self.slotframe_handle,
                u'slotOffset':      cell.slot_offset,
                u'channelOffset':   cell.channel_offset,
                u'neighbor':        cell.mac_addr,
                u'cellOptions':     cell.options
            }
        )

    def delete(self, cell):
        assert cell.slot_offset < self.length
        assert cell in self.slots[cell.slot_offset]
        assert cell in self.cells[cell.mac_addr]
        self.slots[cell.slot_offset].remove(cell)
        self.cells[cell.mac_addr].remove(cell)
        if len(self.cells[cell.mac_addr]) == 0:
            del self.cells[cell.mac_addr]
        if len(self.slots[cell.slot_offset]) == 0:
            del self.slots[cell.slot_offset]

        # log
        self.log(
            SimEngine.SimLog.LOG_TSCH_DELETE_CELL,
            {
                u'_mote_id':        self.mote_id,
                u'slotFrameHandle': self.slotframe_handle,
                u'slotOffset':      cell.slot_offset,
                u'channelOffset':   cell.channel_offset,
                u'neighbor':        cell.mac_addr,
                u'cellOptions':     cell.options,
            }
        )

    def get_cells_by_slot_offset(self, slot_offset):
        assert slot_offset < self.length
        if slot_offset in self.slots:
            return self.slots[slot_offset]
        else:
            return []

    def get_cells_at_asn(self, asn):
        slot_offset = asn % self.length
        return self.get_cells_by_slot_offset(slot_offset)

    def get_cells_by_mac_addr(self, mac_addr):
        if mac_addr in self.cells:
            return self.cells[mac_addr][:]
        else:
            return []

    def get_busy_slots(self):
        busy_slots = list(self.slots.keys())
        # busy_slots.sort()
        return busy_slots

    def get_num_slots_to_next_active_cell(self, asn):
        diff = 1
        while diff <= self.length:
            slot_offset = (asn + diff) % self.length
            if slot_offset in self.slots:
                return diff
            diff += 1
        return None

    def get_available_slots(self):
        """
        Get the list of slot offsets that are not being used (no cell attached)
        :return: a list of slot offsets (int)
        :rtype: list
        """
        all_slots = set(range(self.length))
        return list(all_slots - set(self.get_busy_slots()))

    def get_cells_filtered(self, mac_addr="", cell_options=None):
        """
        Returns a filtered list of cells
        Filtering can be done by cell options, mac_addr or both
        :param mac_addr: the neighbor mac_addr
        :param cell_options: a list of cell options
        :rtype: list
        """

        if mac_addr == "":
            target_cells = chain.from_iterable(list(self.slots.values()))
        elif mac_addr not in self.cells:
            target_cells = []
        else:
            target_cells = self.cells[mac_addr]

        if cell_options is None:
            condition = lambda c: True
        else:
            condition = lambda c: sorted(c.options) == sorted(cell_options)

        # apply filter
        return list(filter(condition, target_cells))

    def set_length(self, new_length):
        # delete extra cells and slots if reducing slotframe length
        if new_length < self.length:
            # delete cells

            slot_offset = new_length
            while slot_offset < self.length:
                if slot_offset in self.slots:
                    for cell in self.slots[slot_offset]:
                        self.delete(cell)
                slot_offset += 1

        # apply the new length
        self.length = new_length

class Cell(object):
    def __init__(
            self,
            slot_offset,
            channel_offset,
            options,
            mac_addr=None,
            link_type=d.LINKTYPE_NORMAL
        ):

        # FIXME: is_advertising is not used effectively now

        # slot_offset and channel_offset are 16-bit values
        assert slot_offset    < 0x10000
        assert channel_offset < 0x10000

        self.slot_offset    = slot_offset
        self.channel_offset = channel_offset
        self.options        = options
        self.mac_addr       = mac_addr
        self.link_type      = link_type

        # back reference to slotframe; this will be set in SlotFrame.add()
        self.slotframe = None

        # stats
        self.num_tx     = 0
        self.num_tx_ack = 0
        self.num_rx     = 0

    def __repr__(self):

        return u'cell({0})'.format(
            u', '.join(
                [
                    u'slot_offset: {0}'.format(self.slot_offset),
                    u'channel_offset: {0}'.format(self.channel_offset),
                    u'mac_addr: {0}'.format(self.mac_addr),
                    u'options: [{0}]'.format(', '.join(self.options)),
                    u'link_type: {0}'.format(self.link_type)
                ]
            )
        )

    def __eq__(self, other):
        return str(self) == str(other)

    def increment_num_tx(self):
        self.num_tx += 1

        # Seciton 5.3 of draft-ietf-6tisch-msf-00: "When NumTx reaches 256,
        # both NumTx and NumTxAck MUST be divided by 2.  That is, for example,
        # from NumTx=256 and NumTxAck=128, they become NumTx=128 and
        # NumTxAck=64. This operation does not change the value of the PDR, but
        # allows the counters to keep incrementing.
        if self.num_tx == 256:
            self.num_tx /= 2
            self.num_tx_ack /= 2

    def increment_num_tx_ack(self):
        self.num_tx_ack += 1

    def increment_num_rx(self):
        self.num_rx += 1

    def is_tx_on(self):
        return d.CELLOPTION_TX in self.options

    def is_rx_on(self):
        return d.CELLOPTION_RX in self.options

    def is_shared_on(self):
        return d.CELLOPTION_SHARED in self.options
