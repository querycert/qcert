#!/usr/bin/env python

# Thanks to Erik for the initial script and sharing his expertise.

import sys
import json
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

def mk_df(mk_line):
    acc = []
    for e in data:
        acc.append(mk_line(e))
    df = pd.DataFrame(data=acc)
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
  #                'SQL -> NRAEnv -> NRA': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_no_optim']['nra_size'],
  #                'SQL -> NRAEnv': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_size'],
  #                'SQL -> NRAEnv -> NRA -> NRA optim': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_optim']['nra_size'],
  #                'SQL -> NRAEnv -> NRAEnv optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_size']
  #            }
  # )
  # df = df.set_index('Queries')
  # axs = df.plot(title='NRA vs NRAEnv: size ('+filename+')',kind='bar')
  # plt.show()

  # df = mk_df(lambda experiment :
  #            {
  #                'Queries': experiment['name'],
  #                'SQL -> NRAEnv -> NRA': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_no_optim']['nra_depth'],
  #                'SQL -> NRAEnv': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_depth'],
  #                'SQL -> NRAEnv -> NRA -> NRA optim': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_optim']['nra_depth'],
  #                'SQL -> NRAEnv -> NRAEnv optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_depth']
  #            }
  # )
  # df = df.set_index('Queries')
  # axs = df.plot(title='NRA vs NRAEnv: depth ('+filename+')',kind='bar')
  # plt.show()


  # ## SQL to NRA
  # df = mk_df(lambda experiment :
  #            {
  #                'Queries': experiment['name'],
  #                # 'SQL -> NRA': experiment['stats']['sql_to_nra']['nra_no_optim']['nra_size'],
  #                # 'SQL -> NRA -> NRA optim': experiment['stats']['sql_to_nra']['nra_optim']['nra_size'],
  #                # 'SQL -> NRAEnv -> NRA': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_no_optim']['nra_size'],
  #                'SQL -> NRAEnv -> NRA -> NRA optim': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_optim']['nra_size'],
  #                'SQL -> NRAEnv -> NRAEnv optim -> NRA -> NRA optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nra']['nra_optim']['nra_size'],
  #            }
  # )
  # df = df.set_index('Queries')
  # axs = df.plot(title='SQL to NRA: size ('+filename+')', kind='bar')
  # plt.show()

  # df = mk_df(lambda experiment :
  #            {
  #                'Queries': experiment['name'],
  #                # 'SQL -> NRA': experiment['stats']['sql_to_nra']['nra_no_optim']['nra_depth'],
  #                # 'SQL -> NRA -> NRA optim': experiment['stats']['sql_to_nra']['nra_optim']['nra_depth'],
  #                # 'SQL -> NRAEnv -> NRA': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_no_optim']['nra_depth'],
  #                'SQL -> NRAEnv -> NRA -> NRA optim': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_to_nra']['nra_optim']['nra_depth'],
  #                'SQL -> NRAEnv -> NRAEnv optim -> NRA -> NRA optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nra']['nra_optim']['nra_depth'],
  #            }
  # )
  # df = df.set_index('Queries')
  # axs = df.plot(title='SQL to NRA: depth ('+filename+')', kind='bar')
  # plt.show()


  # ## SQL to NNRC
  # df = mk_df(lambda experiment :
  #            {
  #                'Queries': experiment['name'],
  #                # 'SQL -> NRA -> NRA optim -> NNRC': experiment['stats']['sql_to_nra']['nra_optim']['nra_to_nnrc']['nnrc_no_optim']['nnrc_size'],
  #                'SQL -> NRAEnv -> NRAEnv optim -> NNRC': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
  #                'SQL -> NRAEnv -> NRAEnv optim -> NRA -> NRA optim -> NNRC': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nra']['nra_optim']['nra_to_nnrc']['nnrc_no_optim']['nnrc_size'],
  #            }
  # )
  # df = df.set_index('Queries')
  # axs = df.plot(title='SQL to NNRC ('+filename+')', kind='bar')
  # plt.show()


  ## SQL to NNRC (size)
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 'SQL': experiment['stats']['sql_size'],
                 'SQL -> NRAEnv': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_size'],
                 'SQL -> NRAEnv -> NRAEnv optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_size'],
                 'SQL -> NRAEnv -> NRAEnv optim -> NNRC': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 'SQL -> NRAEnv -> NRAEnv optim -> NNRC -> NNRC optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim']['nnrc_size'],
             }
  )
  df = df.set_index('Queries')
  axs = df.plot(title='SQL to NNRC ('+filename+')', kind='bar')
  axs.set(ylabel='Query size')
  plt.show()

  ## SQL to NNRC (depth)
  df = mk_df(lambda experiment :
             {
                 'Queries': experiment['name'],
                 'SQL': experiment['stats']['sql_depth'],
                 'SQL -> NRAEnv': experiment['stats']['sql_to_nraenv']['nraenv_no_optim']['nraenv_depth'],
                 'SQL -> NRAEnv -> NRAEnv optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_depth'],
                 # 'SQL -> NRAEnv -> NRAEnv optim -> NNRC': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_no_optim']['nnrc_size'],
                 # 'SQL -> NRAEnv -> NRAEnv optim -> NNRC -> NNRC optim': experiment['stats']['sql_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim']['nnrc_size'],
             }
  )
  df = df.set_index('Queries')
  axs = df.plot(title='SQL to NNRC ('+filename+')', kind='bar')
  axs.set(ylabel='Query depth')
  plt.show()


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
  df.rename(index=str, columns={'1: SQL -> NRAEnv': 'SQL -> NRAEnv',
                                '2: NRAEnv -> NRAEnv optim': 'NRAEnv -> NRAEnv optim',
                                '3: NRAEnv optim -> NNRC': 'NRAEnv optim -> NNRC',
                                '4: NNRC -> NNRC optim': 'NNRC -> NNRC optim' }, inplace=True)
  axs = df.plot(title='SQL to NNRC ('+filename+')', kind='bar', stacked=True)
  axs.set(ylabel='Compilation time (s)')
  plt.show()



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

