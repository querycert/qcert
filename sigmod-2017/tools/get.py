#!/usr/bin/env python

import sys
import json

filename = sys.argv[1]
with open(filename) as data_file:
  data = json.load(data_file)
  # print(data['rule_to_nraenv']['nraenv_no_optim']['nraenv_string'])
  # print(data['rule_to_nraenv']['nraenv_optim']['nraenv_string'])
  # print(data['rule_to_nraenv']['nraenv_optim']['nraenv_to_nra']['nra_optim']['nra_string'])

  print(data['rule_to_nra']['nra_no_optim']['nra_string'])
  # print(data['rule_to_nra']['nra_optim']['nra_string'])


  # print(data['rule_to_nraenv']['nraenv_optim']['nraenv_to_nnrc']['nnrc_optim_string'])
