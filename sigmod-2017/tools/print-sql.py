#!/usr/bin/env python

# Thanks to Erik for the initial script and sharing his expertise.

import sys
import json
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
# from matplotlib import pyplot as plt
# import matplotlib as mpl
# mpl.rcParams['text.usetex'] = True

def mk_df(mk_line):
    acc = []
    for e in data:
        acc.append(mk_line(e))
    df = pd.DataFrame(acc)
    # print df
    return df

filename = sys.argv[1]
with open(filename) as data_file:
  data = json.load(data_file)

  ## SQL to NNRC size
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 '1: SQL': experiment['stats']['sql_size'],
                 '2: NRA$^{\mathbf{e}}$': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_size'],
                 '3: NRA$^{\mathbf{e}}$ optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_size'],
                 '4: NNRC': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 '5: NNRC optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim']['nnrc_size'],
             }
  )
  df = df.set_index('Queries')
  df.rename(index=str, columns={'1: SQL': 'SQL size',
                                '2: NRA$^{\mathbf{e}}$': 'NRA$^{\mathbf{e}}$ query size',
                                '3: NRA$^{\mathbf{e}}$ optim': 'NRA$^{\mathbf{e}}$ opt query size',
                                '4: NNRC': 'NNRC query size',
                                '5: NNRC optim':'NNRC opt query size' }, inplace=True)
  axs = df.plot(kind='bar', color=['y', 'b', 'r', 'g', 'k'], edgecolor = "none", width=0.8, figsize=(9.5,6.1))
  # axs.set(ylabel='Query size')
  axs.set(xlabel='',ylabel='')
  axs.set_ylim([0,330])

  bars = axs.patches
  # patterns = ''.join(h*len(df) for h in ' |x+.')
  # for bar, pattern in zip(bars, patterns):
  #   bar.set_hatch(pattern)
  axs.legend(loc='upper left')

  # plt.show()
  fig = axs.get_figure()
  output = '%s_size.pdf' % filename
  fig.savefig(output,bbox_inches='tight')

  ## SQL to NNRC depth
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 '1: SQL': experiment['stats']['sql_depth'],
                 '2: NRA$^{\mathbf{e}}$': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_depth'],
                 '3: NRA$^{\mathbf{e}}$ optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_depth'],
                 # '4: NNRC': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 # '5: NNRC optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim']['nnrc_size'],
             }
  )
  df = df.set_index('Queries')
  df.rename(index=str, columns={'1: SQL': 'SQL query depth',
                                '2: NRA$^{\mathbf{e}}$': 'NRA$^{\mathbf{e}}$ query depth',
                                '3: NRA$^{\mathbf{e}}$ optim': 'NRA$^{\mathbf{e}}$ opt query depth',
                                # '4: NNRC': 'NNRC',
                                # '5: NNRC optim':'NNRC opt'
  }, inplace=True)
  axs = df.plot(kind='bar', color=['y', 'b', 'r', 'g', 'k'], edgecolor = "none", width=0.8)
  # axs.set(ylabel='Query depth')
  axs.set(xlabel='',ylabel='')
  ylim = axs. get_ylim()
  # axs.set_ylim([0,ylim[1]+1])
  plt.yticks(np.arange(0, ylim[1]+2, 1.0))

  bars = axs.patches
  # patterns = ''.join(h*len(df) for h in ' |x+.')
  # for bar, pattern in zip(bars, patterns):
  #   bar.set_hatch(pattern)
  axs.legend(loc='upper left')

  # plt.show()
  fig = axs.get_figure()
  output = '%s_depth.pdf' % filename
  fig.savefig(output,bbox_inches='tight')


  ## Timing
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 '1: SQL -> NRAEnv': float(experiment['stats']['sql_to_nraenv_time']),
                 '2: NRAEnv -> NRAEnv optim': float(experiment['stats']['sql_to_nraenv']['nraenv_optim_time']),
                 '3: NRAEnv optim -> NNRC': float(experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc_time']),
                 '4: NNRC -> NNRC optim': float(experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim_time']),
             }
  )
  df = df.set_index('Queries')
  df.rename(index=str, columns={'1: SQL -> NRAEnv': 'SQL to NRA$^{\mathbf{e}}$',
                                '2: NRAEnv -> NRAEnv optim': 'NRA$^{\mathbf{e}}$ to NRA$^{\mathbf{e}}$ opt',
                                '3: NRAEnv optim -> NNRC': 'NRA$^{\mathbf{e}}$ opt to NNRC',
                                '4: NNRC -> NNRC optim': 'NNRC to NNRC opt' }, inplace=True)
  axs = df.plot(kind='bar', stacked=True, color=['b', 'r', 'g', 'k'], edgecolor = "none", width=0.8)
  # axs.set(ylabel='Compilation time (s)')
  axs.set(xlabel='',ylabel='')
  axs.set_ylim([0,0.6])

  bars = axs.patches
  # patterns = ''.join(h*len(df) for h in '|x+.')
  # for bar, pattern in zip(bars, patterns):
  #   bar.set_hatch(pattern)
  axs.legend(loc='upper left')

  # plt.show()
  fig = axs.get_figure()

  output = '%s_timing.pdf' % filename
  fig.savefig(output,bbox_inches='tight')


# create pandas dataframe:
# df = pd.read_csv(file_name, index_col=[0])
# average = df.mean(axis=1)

# # plt.figure()

# # plot results:
# axes = df.plot(title='Availability ' + port + '://' + api)
# axes.legend(bbox_to_anchor=(1, 0.5))
# axes.set_ylim(0,700)
# axes.set_ylabel('HTTP status code')
# axes.set_xlabel('Seconds since start')
# fig = axes.get_figure()
# output = '%s/availability_%s_%s.png' % (output_folder, port, api)
# fig.savefig(output)

# # new plot:
# plt.figure()

# # plot average:
# axes2 = average.plot(title='Average availability ' + port + '://' + api)
# axes2.set_ylim(0,700)
# axes2.set_ylabel('Average HTTP status code')
# axes2.set_xlabel('Seconds since start')
# fig2 = axes2.get_figure()
# output2 = '%s/availability_%s_%s_average.png' % (output_folder, port, api)
# fig2.savefig(output2)

