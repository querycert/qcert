#!/usr/bin/env python

# Thanks to Erik Wittern for the initial script and sharing his expertise.

import sys
import json
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

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

  ## CAMP to NNRC size
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 # '1: CAMP': experiment['stats']['rule_size'],
                 '2: NRA$^{\mathbf{e}}$': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_size'],
                 '3: NRA$^{\mathbf{e}}$ optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_size'],
                 '4: NNRC': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 '5: NNRC optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim']['nnrc_size'],
             }
  )
  df = df.set_index('Queries')
  df.rename(index=str, columns={# '1: CAMP': 'CAMP',
                                '2: NRA$^{\mathbf{e}}$': 'NRA$^{\mathbf{e}}$ query size',
                                '3: NRA$^{\mathbf{e}}$ optim': 'NRA$^{\mathbf{e}}$ opt query size',
                                '4: NNRC': 'NNRC query size',
                                '5: NNRC optim':'NNRC opt query size' }, inplace=True)
  axs = df.plot(kind='bar', color=['b', 'r', 'g', 'k', 'y'], edgecolor = "none", width=0.8)
  axs.set(xlabel='',ylabel='Query size')

  bars = axs.patches
  axs.legend(loc='upper left')

  # plt.show()
  fig = axs.get_figure()
  output = '%s_camp_size.pdf' % filename
  fig.savefig(output,bbox_inches='tight')

  ## CAMP to NNRC depth
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 # '1: CAMP': experiment['stats']['rule_depth'],
                 '2: NRA$^{\mathbf{e}}$': experiment['stats']['rule_to_nraenv']['nraenv_no_optim']['nraenv_depth'],
                 '3: NRA$^{\mathbf{e}}$ optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_depth'],
                 # '4: NNRC': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 # '5: NNRC optim': experiment['stats']['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim']['nnrc_size'],
             }
  )
  df = df.set_index('Queries')
  df.rename(index=str, columns={'1: CAMP': 'CAMP query depth',
                                '2: NRA$^{\mathbf{e}}$': 'NRA$^{\mathbf{e}}$ query depth',
                                '3: NRA$^{\mathbf{e}}$ optim': 'NRA$^{\mathbf{e}}$ opt query depth',
                                # '4: NNRC': 'NNRC',
                                # '5: NNRC optim':'NNRC opt'
  }, inplace=True)
  axs = df.plot(kind='bar', color=['b', 'r', 'g', 'k', 'y'], edgecolor = "none", width=0.8)
  axs.set(xlabel='',ylabel='Query depth')

  bars = axs.patches
  axs.legend(loc='upper left')

  # plt.show()
  fig = axs.get_figure()
  output = '%s_camp_depth.pdf' % filename
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
  axs = df.plot(kind='bar', stacked=True, color=['b', 'r', 'g', 'k', 'y'], edgecolor = "none", width=0.8)
  axs.set(xlabel='',ylabel='Compilation time (s)')

  bars = axs.patches
  axs.legend(loc='upper left')

  fig = axs.get_figure()

  output = '%s_camp_timing.pdf' % filename
  fig.savefig(output,bbox_inches='tight')


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
  axs.set(xlabel='',ylabel='NRA query size')

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
  axs.set(xlabel='',ylabel='NRA query depth')
  axs.set_ylim([0,15])

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
  axs.set(xlabel='',ylabel='NNRC expression size')

  fig = axs.get_figure()
  output = '%s_nnrc_size.pdf' % filename
  fig.savefig(output,bbox_inches='tight')

