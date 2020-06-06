"""
Plot a stat over another stat.

Example:
    python plot.py --inputfolder simData/numMotes_50/ -x chargeConsumed --y aveLatency
"""
from __future__ import print_function

# =========================== imports =========================================

# standard
from builtins import range
import os
import argparse
import json
import glob
from collections import OrderedDict
import numpy as np

# third party
import matplotlib
from matplotlib.ticker import MaxNLocator

matplotlib.use('Agg')
import matplotlib.pyplot as plt
import seaborn as sns  # NPEB_modif
import pandas as pd
from SimEngine.Mote.tsch import DELAY_LOG_AFTER_EB

# ============================ defines ========================================

KPIS = [
    'latency_max_s',
    'latency_avg_s',
    'latencies',
    'lifetime_AA_years',
    'sync_time_s',
    'join_time_s',
    'upstream_num_lost',
    'joinRPL_time_s', # vv NPEB_modif vv
    'charge_synched',
    'charge_joined',
    'charge_joinedRPL',
    'charge_afterEB',
    'first_hop'
]

pretty_names = {
    'latency_max_s': "Maximum latency (s)",
    'latency_avg_s': "Average latency (s)",
    'latencies': "Latencies (s)",
    'lifetime_AA_years': "Estimated lifetime powered by AA battery (year)",
    'sync_time_s': "Synchronization time (s)",
    'join_time_s': "Join time (s)",
    'upstream_num_lost': "Number of upstream packet losses",
    'first_hop': "Number of hops for first packet",
    'joinRPL_time_s': "Time to join RPL topology (s)",
    'charge_synched': "Charge consumed until synchronized (uC)",
    'charge_joined': "Charge consumed until joined (uC)",
    'charge_joinedRPL': "Charge consumed until joined RPL topology (uC)",
    'charge_afterEB': "Charge consumed until %d s after allowed to send EBs (uC)" % (DELAY_LOG_AFTER_EB,)
}

# ============================ main ===========================================

def main(options):

    # init
    data = OrderedDict()

    # chose lastest results
    subfolders = list(
        [os.path.join(options.inputfolder, x) for x in os.listdir(options.inputfolder)]
    )
    subfolder = max(subfolders, key=os.path.getmtime)

    phases_stats = {'times': {}, 'charges': {}}
    global_stats = {'nbr_motes': None, 'nbr_runs': None, 'convergence_times': []}

    for key in options.kpis:
        # load data
        for file_path in sorted(glob.glob(os.path.join(subfolder, '*.kpi'))):
            curr_combination = os.path.basename(file_path)[:-8] # remove .dat.kpi
            with open(file_path, 'r') as f:

                # read kpi file
                kpis = json.load(f)

                # init data list
                data[curr_combination] = []

                # fill data list
                nbr_runs = 0
                conv_times = []
                for run in kpis.values():
                    nbr_runs += 1
                    convergence_time = run['global-stats']['convergence_time']
                    if convergence_time != 'N/A':
                        conv_times.append(convergence_time)
                    nbr_motes = 1  # Root is excluded from logs, add it artificially
                    for mote in run.values():
                        if key in mote:
                            nbr_motes += 1
                            if mote[key] is not None:
                                data[curr_combination].append(mote[key])
                global_stats['nbr_runs'] = nbr_runs
                global_stats['nbr_motes'] = nbr_motes
                global_stats['convergence_times'] = conv_times

        if key in ['sync_time_s', 'join_time_s', 'joinRPL_time_s']:
            phases_stats['times'][key] = data[data.keys()[0]]
        elif key in ['charge_synched', 'charge_joined', 'charge_joinedRPL', 'charge_afterEB']:
            phases_stats['charges'][key] = data[data.keys()[0]]
        # plot
        try:
            if key in ['lifetime_AA_years', 'latencies']:
                plot_cdf(data, key, global_stats, subfolder)
            elif key == 'first_hop':  # NPEB_modif
                plot_histogram_hops(data, global_stats, subfolder)
            elif key == 'charge_joined': # NPEB_modif
                plot_histogram_charge_joined(data, global_stats, subfolder)
            else:
                plot_box(data, key, global_stats,subfolder)

        except TypeError as e:
            print("Cannot create a plot for {0}: {1}.".format(key, e))
    plot_phase_times_boxplots(phases_stats['times'], global_stats, subfolder)
    plot_phase_charges_boxplots(phases_stats['charges'], global_stats, subfolder)
    print("Plots are saved in the {0} folder.".format(subfolder))

# =========================== helpers =========================================

def str_global_stats(global_stats):
    return "Number of nodes : %d   Number of runs : %d (%d converged)"\
           % (global_stats['nbr_motes'], global_stats['nbr_runs'], len(global_stats['convergence_times']))


def write_additional_stats(output_folder, s, filename="add_stats.txt"):
    if not os.path.isdir(output_folder):
        os.makedirs(output_folder)
    with open(output_folder+'/'+filename, 'a+') as f:
        f.write(s)


def plot_phase_times_boxplots(phase_times, global_stats, subfolder):
    conv_times = global_stats['convergence_times']
    if len(conv_times) > 0:
        mean_conv_time = float(sum(conv_times)) / len(conv_times)
    else:
        mean_conv_time = 0
    stat_names = ['sync_time_s', 'join_time_s', 'joinRPL_time_s']
    labels = {stat_names[0]: 'Synchro',
              stat_names[1]: 'SecJoin',
              stat_names[2]: 'RPLjoin'}
    data = {'phase': [], 'value': []}
    for phase, vals in phase_times.items():
        data['phase'].extend([labels[phase]] * len(vals))
        data['value'].extend(vals)

    df = pd.DataFrame(data)
    stats_join_steps = df.groupby('phase').describe().to_string()
    stats_convergence = pd.Series(conv_times).describe().to_string()
    stats_write = "==== Time elapsed at steps of join process - " + str_global_stats(global_stats) + '\n' +\
                  stats_join_steps + '\n\n--- With convergence times stats\n' + stats_convergence + '\n\n\n'
    write_additional_stats(subfolder, stats_write)
    ax = sns.boxplot(y='phase', x='value', data=data, orient='h', linewidth=1,
                     order=[labels[t] for t in stat_names[::-1]],
                     palette=['OrangeRed', 'Orange', 'Gold'],
                     notch=False, meanline=True, showmeans=True)
    ax.set_title("Time elapsed at steps of join process for all nodes\n"+str_global_stats(global_stats))
    # x axis
    ax.set_xlabel("Time (s)")
    # Set a vertical line for mean convergence time
    ax.axvline(mean_conv_time, label="Mean convergence times")

    savefig(subfolder, "phase_times")
    plt.clf()


def plot_phase_charges_boxplots(phase_charges, global_stats, subfolder):
    stat_names = ['charge_synched', 'charge_joined', 'charge_joinedRPL', 'charge_afterEB']
    labels = {stat_names[0]: 'Synchro',
              stat_names[1]: 'SecJoin',
              stat_names[2]: 'RPLjoin',
              stat_names[3]: str(DELAY_LOG_AFTER_EB) + 's after EB'}
    data = {'phase': [], 'value': []}
    for phase, vals in phase_charges.items():
        data['phase'].extend([labels[phase]] * len(vals))
        data['value'].extend(map(lambda microC: microC/1000, vals))

    df = pd.DataFrame(data)
    stats_join_steps = df.groupby('phase').describe().to_string()
    stats_write = "==== Charge consumed at steps of join process - " + str_global_stats(global_stats) + '\n' +\
                  stats_join_steps + '\n\n\n'
    write_additional_stats(subfolder, stats_write)
    ax = sns.boxplot(y='phase', x='value', data=data, orient='h', linewidth=1,
                     palette=['Tomato', 'OrangeRed', 'Orange', 'Gold'],
                     order=[labels[t] for t in stat_names[::-1]],
                     notch=False, meanline=True, showmeans=True)
    ax.set_title("Charge consumed at steps of join process for all nodes\n"+str_global_stats(global_stats))
    # x axis
    ax.set_xlabel("Charge (mC)")

    savefig(subfolder, "phase_charges")
    plt.clf()


#NPEB_modif
def plot_histogram_hops(data, global_stats, subfolder):
    for k, values in data.items():
        ax = sns.distplot(values, kde=False, hist_kws={"align": 'mid'})
        ax.set_title("Distribution of number of hops for the first data traffic of each node\n"+str_global_stats(global_stats))
        ax.minorticks_on()
        # y axis
        ax.set_ylabel("Number of joined nodes")
        ax.yaxis.set_major_locator(MaxNLocator(integer=True))
        ax.grid(axis="y")
        # x axis
        ax.set_xlabel("Number of hops")
        ax.set_xticks(list(set(values)))
        ax.set_xlim(left=min(values)-0.5, right=max(values)+0.5)
        ax.xaxis.set_tick_params(which='minor', bottom=False)

        savefig(subfolder, "firsthop" + ".hist")
        plt.clf()


#NPEB_modif
def plot_histogram_charge_joined(data, global_stats, subfolder):
    for k, values in data.items():
        values = map(lambda microC: microC/1000, values)
        ax = sns.distplot(values, bins=20, kde=False, hist_kws={"align": 'mid'}, rug=True)
        ax.set_title("Distribution of consumed charge values at joining achievement\n"+str_global_stats(global_stats))
        ax.minorticks_on()
        # y axis
        ax.yaxis.set_major_locator(MaxNLocator(integer=True))
        ax.yaxis.set_tick_params(which='minor', bottom=False)
        ax.grid(axis="y")
        # x axis
        ax.set_xlabel("Charge value (mC)")

        savefig(subfolder, "chargejoined" + ".hist")
        plt.clf()


def plot_cdf(data, key, global_stats, subfolder):
    for k, values in data.items():
        # convert list of list to list
        if type(values[0]) == list:
            values = sum(values, [])

        values = [None if value == 'N/A' else value for value in values]
        # compute CDF
        sorted_data = np.sort(values)
        yvals = np.arange(len(sorted_data)) / float(len(sorted_data) - 1)
        plt.plot(sorted_data, yvals, label=k)

    plt.xlabel(pretty_names[key])
    plt.ylabel("CDF")
    plt.grid(axis='y')
    plt.title("CDF for the KPI : " + pretty_names[key] + "\n" + str_global_stats(global_stats))
    savefig(subfolder, key + ".cdf")
    plt.clf()

def plot_box(data, key, global_stats, subfolder):
    name = "Means on %d runs" % (global_stats['nbr_runs'],)
    plt.boxplot(list(data.values()))
    plt.xticks(list(range(1, len(data) + 1)), [name]*len(data))
    plt.ylabel(pretty_names[key])
    plt.title("Distribution for the KPI : " + pretty_names[key] + '\n' + str_global_stats(global_stats))
    savefig(subfolder, key)
    plt.clf()


def savefig(output_folder, output_name, output_format="png"):
    # check if output folder exists and create it if not
    if not os.path.isdir(output_folder):
        os.makedirs(output_folder)

    # save the figure
    plt.savefig(
        os.path.join(output_folder, output_name + "." + output_format),
        bbox_inches     = 'tight',
        pad_inches      = 0,
        format          = output_format,
    )

def parse_args():
    # parse options
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--inputfolder',
        help       = 'The simulation result folder.',
        default    = 'simData',
    )
    parser.add_argument(
        '-k','--kpis',
        help       = 'The kpis to plot',
        type       = list,
        default    = KPIS
    )
    parser.add_argument(
        '--xlabel',
        help       = 'The x-axis label',
        type       = str,
        default    = None,
    )
    parser.add_argument(
        '--ylabel',
        help       = 'The y-axis label',
        type       = str,
        default    = None,
    )
    parser.add_argument(
        '--show',
        help       = 'Show the plots.',
        action     = 'store_true',
        default    = None,
    )
    return parser.parse_args()

if __name__ == '__main__':

    options = parse_args()

    main(options)
