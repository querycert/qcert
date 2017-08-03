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

