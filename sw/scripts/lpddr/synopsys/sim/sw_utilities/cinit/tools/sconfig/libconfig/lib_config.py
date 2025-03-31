#!/usr/bin/env python3
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
# -------------------------------------------------------------------------------



# Local
import libconfig.types.category as cat
from libconfig.utils import Singleton


class LibConfig(metaclass = Singleton):
    def __init__(self):
        self.db_config = cat.Category(name='Config')

    def get_config_db(self):
        """ Get config database root """

        return self.db_config

    def add_category(self, category):
        """ Add category to root """

        self.db_config.add_child_category(category)

    def find_config_by_id(self, id):
        """ Find config parameter by id
            requires indexing """

        return self.db_config_index.get(id)

    def list_parameters(self):
        """ List all parameters """

        return self.list_configs(self.db_config)

    def print_parameters(self):
        """ Print all parameters according to the database hierarchy """

        print(self.db_config)

    def list_configs(self, parent):
        """ List all configs in the hierarchy under a category """

        ret_list = []
        for child_config in parent.child_configs:
            ret_list.append(child_config)
        for child_cat in parent.child_categories:
            ret_list += self.list_configs(child_cat)
        return ret_list

    def index_config_db(self):
        """ Index config database """

        # create db_config_index
        self.db_config_index = {}
        for config in self.list_parameters():
            if (config.get_id() is not None):
                self.db_config_index[config.get_id()] = config

            for option in config.list_options():
                self.db_config_index[option.get_id()] = option

    def get_config_dict(self):
        """ Get a dictionary with all configuration parameters mapped to their IDs """

        return self.db_config_index
