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
  # print json.dumps(data, indent=2)

  # ## NRA vs NRAEnv
  # df = mk_df(lambda experiment :
  #            {
  #                'Queries': experiment['name'],
  #                'CAMP -> NRA': experiment['stats']['rule_to_nra']['nra_no_optim']['nra_size'],
  #                'CAMP -> NRAEnv': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_size'],
  #                'CAMP -> NRA -> NRA optim': experiment['stats']['rule_to_nra']['nra_optim']['nra_size'],
  #                'CAMP -> NRAEnv -> NRAEnv optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_size']
  #            }
  # )
  # df = df.set_index('Queries')
  # axs = df.plot(title='NRA vs NRAEnv: size ('+filename+')',kind='bar')
  # plt.show()

  # df = mk_df(lambda experiment :
  #            {
  #                'Queries': experiment['name'],
  #                'CAMP -> NRA': experiment['stats']['rule_to_nra']['nra_no_optim']['nra_depth'],
  #                'CAMP -> NRAEnv': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_depth'],
  #                'CAMP -> NRA -> NRA optim': experiment['stats']['rule_to_nra']['nra_optim']['nra_depth'],
  #                'CAMP -> NRAEnv -> NRAEnv optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_depth']
  #            }
  # )
  # df = df.set_index('Queries')
  # axs = df.plot(title='NRA vs NRAEnv: depth ('+filename+')',kind='bar')
  # plt.show()


  ## CAMP to NRA
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 # 'CAMP -> NRA': experiment['stats']['rule_to_nra']['nra_no_optim']['nra_size'],
                 # 'CAMP -> NRA -> NRA optim': experiment['stats']['rule_to_nra']['nra_optim']['nra_size'],
                 # 'CAMP -> NRAEnv -> NRA': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_no_optim']['nra_size'],
                 # 'CAMP -> NRAEnv -> NRA -> NRA optim': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_optim']['nra_size'],
                 # 'CAMP -> NRAEnv -> NRAEnv optim -> NRA -> NRA optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nra']['nra_optim']['nra_size'],
                 r'NRA query size through NRA': experiment['stats']['rule_to_nra']['nra_optim']['nra_size'],
                 r'NRA query size through NRA$^{\mathbf{e}}$': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nraenv_core']['nraenv_core_optim']['nraenv_core_to_nra']['nra_optim']['nra_size'],

             }
  )
  df = df.set_index('Queries')
  axs = df.plot(kind='bar', color=['c', 'm'], edgecolor = "none", width=0.8)
  # axs.set(ylabel='NRA query size')
  axs.set(xlabel='',ylabel='')

  # plt.show()
  fig = axs.get_figure()
  output = '%s_nra_size.pdf' % filename
  fig.savefig(output,bbox_inches='tight')



  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 # 'CAMP -> NRA': experiment['stats']['rule_to_nra']['nra_no_optim']['nra_depth'],
                 # 'CAMP -> NRA -> NRA optim': experiment['stats']['rule_to_nra']['nra_optim']['nra_depth'],
                 # 'CAMP -> NRAEnv -> NRA': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_no_optim']['nra_depth'],
                 # 'CAMP -> NRAEnv -> NRA -> NRA optim': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_optim']['nra_depth'],
                 # 'CAMP -> NRAEnv -> NRAEnv optim -> NRA -> NRA optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nra']['nra_optim']['nra_depth'],
                 r'NRA query depth through NRA': experiment['stats']['rule_to_nra']['nra_optim']['nra_depth'],
                 r'NRA query depth through NRA$^{\mathbf{e}}$': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nraenv_core']['nraenv_core_optim']['nraenv_core_to_nra']['nra_optim']['nra_depth'],
             }
  )
  df = df.set_index('Queries')
  axs = df.plot(kind='bar', color=['c', 'm'], edgecolor = "none", width=0.8)
  # axs.set(ylabel='NRA query depth')
  axs.set(xlabel='',ylabel='')
  axs.set_ylim([0,15])

  # plt.show()
  fig = axs.get_figure()
  output = '%s_nra_depth.pdf' % filename
  fig.savefig(output,bbox_inches='tight')


  ## CAMP to NNRC
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 # 'CAMP -> NRA -> NRA optim -> NNRC': experiment['stats']['rule_to_nra']['nra_optim']['nra_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 # 'CAMP -> NRAEnv -> NRAEnv optim -> NNRC': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 # 'CAMP -> NRAEnv -> NRAEnv optim -> NRA -> NRA optim -> NNRC': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nra']['nra_optim']['nra_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 r'NNRC query size through NRA': experiment['stats']['rule_to_nra']['nra_optim']['nra_to_nnrc_core']['nnrc_core_optim']['nnrc_core_size'],
                 r'NNRC query size through NRA$^{\mathbf{e}}$': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim']['nnrc_size'],
             }
  )
  df = df.set_index('Queries')
  axs = df.plot(kind='bar', color=['w', 'k'], width=0.8)
  # axs.set(ylabel='NNRC expression size')
  axs.set(xlabel='',ylabel='')

  # plt.show()
  fig = axs.get_figure()
  output = '%s_nnrc_size.pdf' % filename
  fig.savefig(output,bbox_inches='tight')

  ## Timing
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 '1: CAMP -> NRAEnv': float(experiment['stats']['rule_to_nraenv_time']),
                 '2: NRAEnv -> NRAEnv optim': float(experiment['stats']['rule_to_nraenv']['nraenv_optim_time']),
                 '3: NRAEnv optim -> NNRC': float(experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc_time']),
                 '4: NNRC -> NNRC optim': float(experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim_time']),
             }
  )
  df = df.set_index('Queries')
  df.rename(index=str, columns={'1: CAMP -> NRAEnv': 'CAMP to NRA$^{\mathbf{e}}$',
                                '2: NRAEnv -> NRAEnv optim': 'NRA$^{\mathbf{e}}$ to NRA$^{\mathbf{e}}$ optim',
                                '3: NRAEnv optim -> NNRC': 'NRA$^{\mathbf{e}}$ optim to NNRC',
                                '4: NNRC -> NNRC optim': 'NNRC to NNRC optim' }, inplace=True)
  axs = df.plot(kind='bar', stacked=True, cmap='Dark2', width=0.8)
  # axs.set(ylabel='Compilation time (s)')
  axs.set(xlabel='',ylabel='')

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

