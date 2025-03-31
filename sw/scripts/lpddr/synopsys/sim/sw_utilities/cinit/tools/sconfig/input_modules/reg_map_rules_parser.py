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



import os
import copy
from lxml import etree


# Local
from libconfig.log import Log


class RulesParserError(Exception):
    def __init__(self, message):
        super().__init__(message)

class RuleParam():
    def __init__(self, name, min, max):
        self.name    = name
        self.min     = int(min)
        self.max     = int(max)


class RegRule():
    def __init__(self, block, reg_name, field_name, action, depends):
        self.block      = block
        self.reg_name   = reg_name
        self.field_name = field_name
        self.action     = action
        self.depends    = depends
        self.children   = []
        # print(self.get_id() + " " + str(self.depends))

    def get_id(self):
        if self.block is None:
            return "ROOT"
        id_str  = "DWC_DDRCTL_CINIT_" + str(self.block.upper())
        if self.reg_name is None:
            return id_str
        id_str += "_" + str(self.reg_name.upper())
        if self.field_name is None:
            return id_str
        return id_str + "_" + str(self.field_name.upper())

    def is_exclude(self):
        return self.action == "exclude"

    def is_allow(self):
        return self.action == "allow"

    def is_depends(self):
        return self.action == "depend"

    def get_depends(self):
        if self.is_depends():
            return self.depends
        if self.is_exclude():
            return "0"

    def get_block(self):
        return self.block

    def get_register(self):
        return self.reg_name

    def get_field(self):
        return self.field_name

    def add_rule(self, rule):
       self.children.append(rule)

    def get_rules(self):
       return self.children

    def print(self):
        print("block: %s reg %s field %s" % (self.block, self.reg_name, self.field_name))
        for child in self.children:
            child.print()


class RegMapRulesParser():
    rule_dict = {}
    rule_tree = None

    def __init__(self, reg_rules_xml):
        """ Rules parser initialization receiving the rules xml file"""

        if os.path.isfile(reg_rules_xml) is False:
            raise RulesParserError("Register rules file not found")
        rule_xml_tree = etree.parse(reg_rules_xml).getroot()
        self.rule_tree = self._read_rules(rule_xml_tree)

    def get_rule(self, id):
        return self.rule_dict.get(id)


    def _translate_expression(expression):
        """ Transform expressions from RegMapRules format to config tool format """
        if expression is None:
            return expression
        expression = expression.replace(" gt ", " > ")
        expression = expression.replace(" lt ", " < ")
        expression = expression.replace("{", "(")
        expression = expression.replace("}", ")")
        expression = expression.replace("&&", " and ")
        expression = expression.replace("||", " or ")
        return expression

    def _read_params(self, xml_param):
        """ Load param data from an xml object """

        name    = xml_param.attrib['name']
        min     = xml_param.attrib['min']
        max     = xml_param.attrib['max']
        return RuleParam(name=name, min=min, max=max)

    def _expand_rule(self, parent, xml_rule, param):
        """ Expand the rule using the first param found and read the new rules created """

        rule_param = self._read_params(param)
        xml_rule.remove(param)
        for index in range(rule_param.min, rule_param.max + 1):
            xml_clone = copy.deepcopy(xml_rule)
            replace_str = "{%s}" % rule_param.name
            # Change elements at top level
            for element in xml_clone.findall("."):
                for prop in element.attrib:
                    element.attrib[prop] = element.attrib[prop].replace(replace_str, str(index))
            # Change child elements
            for element in xml_clone.findall(".//"):
                for prop in element.attrib:
                    element.attrib[prop] = element.attrib[prop].replace(replace_str, str(index))
            self._read_rules(xml_rule=xml_clone, parent=parent)

    def _read_rules(self, xml_rule, parent=None):
        """ Read the rule tree passed and add the rule to the class"""

        param = xml_rule.find('param')
        if param is not None:
            # If there are params for the rule, will expand and process
            self._expand_rule(parent, xml_rule, param)
            return

        block    = xml_rule.attrib.get('block')
        register = xml_rule.attrib.get('register')
        field    = xml_rule.attrib.get('field')
        action   = xml_rule.attrib.get('action')
        depends  = xml_rule.attrib.get('depends')

        parent_block = None
        parent_register = None
        if parent is not None:
            parent_block    = parent.get_block()
            parent_register = parent.get_register()

        if block is None:
            block = parent_block
        else:
            if (parent_block is not None) and (parent_block != block):
                raise RulesParserError("Rule block (%s) don't match parent (%s)" %
                                (block, parent_block))

        if register is None:
            register = parent_register
        else:
            if (parent_register is not None) and (parent_register != register):
                raise RulesParserError("Rule register (%s) don't match parent (%s)" %
                                            (register, parent_register))

        depends = RegMapRulesParser._translate_expression(depends)

        rule = RegRule(block=block, reg_name=register, field_name=field, action=action, depends=depends)
        self.rule_dict[rule.get_id()] = rule

        for child_rule_xml in xml_rule.findall('./rule'):
            self._read_rules(xml_rule=child_rule_xml, parent=rule)
