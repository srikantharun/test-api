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
import sys
import re

from libconfig.lib_config import LibConfig
from libconfig.types.eval_expressions import EvalExpressions

class GenHTMLDoc():

    def __init__(self):
        self.lib_config = LibConfig()
        self.categories_to_index = []

    def gen_doc(self, output_dir, show_all):
        """ Generate documentation """

        # get database
        config_db = self.lib_config.get_config_db()

        # create output dir if necessary
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)

        top_level_categories = config_db.list_child_categories()

        # for each category in root
        for category in top_level_categories:
            # build path for the documentation this category
            output_filename = category.get_name().replace(' ', '_').lower() + '.html'
            output_path = os.path.join(output_dir, output_filename)

            # generate documentation this category
            self.gen_doc_file(output_path, category, show_all)

        # generate index
        self.gen_index(output_dir)

    def gen_doc_file(self, output_path, category, show_all):
        """ Generate a documentation file with the data from a category """

        # Generate table of for a category
        category_content=self.gen_doc_category_table(category, show_all)
        if (category_content == None):
            return

        with open(output_path,'w') as out_file:
            out_file.write(self.start_report())
            out_file.write(category_content)
            out_file.write(self.end_report())

        print("Generation Successful:", output_path)
        self.categories_to_index.append(category)

    def gen_index(self, output_dir):
        """ Generate HTML index file """

        output_path = os.path.join(output_dir, 'index.html')

        with open(output_path,'w') as out_file:
            out_file.write(self.start_report())

            # generate header
            out_file.write("<h2>Index</h2><ul>")
            for category in self.categories_to_index:
                # generate each link
                category_filename = category.get_name().replace(' ', '_').lower() + '.html'
                out_file.write("<h3><li><a href=\"%s\">%s</a></li></h3>" % (category_filename, category.get_name()))
            out_file.write("</ul>")

            out_file.write(self.end_report())
        print("Generation Successful:", output_path)

    def gen_doc_category_table(self, category, show_all):
        """ Generate a table with the data of a category """

        category_content=self.gen_doc_category(category, show_all)
        if (category_content == ''):
            return None

        category_table="<div class=\"table_report\">\n"

        # Page Title
        category_table+="<h2>\n"
        category_table+=category.get_name()
        category_table+="<a class=\"page_button_close\"\">&#9650;</a><a class=\"page_button_open\"\">&#9660;</a>"
        category_table+="</h2>\n"

        # Index link
        category_table+="<h3><a href=\"index.html\">Index</a></h3>"

        category_table+="<div style=\"overflow-x:auto;\">\n"
        category_table+=category_content
        category_table+="</table>\n</div>\n</div>"

        return category_table

    def gen_doc_category(self, category, show_all, indent=0):
        """ Generate the rows of a table for a category """

        content = ''
        for child in category.list_child_configs():
            content +=self.gen_doc_config(child, show_all)

        for child in category.list_child_categories():
            sub_cat = self.gen_doc_category(child, show_all, indent + 1)
            if sub_cat != '':
                content += "<tr><td colspan=\"2\" class=\"row_with_table\">" + sub_cat + "</td></tr>"
        
        if content == '':
            return ''

        category_indent = ''
        if (indent > 0):
            category_indent = '&nbsp;&nbsp;&nbsp;&nbsp;'*indent + '&#9492; '
        cat_buttons="<a class=\"cat_button_close\"\">&#128897;</a><a class=\"cat_button_open\"\">&#128899;</a>"

        out = "<table>"
        out += "<thead>\n<th>%s&nbsp;&nbsp;%s%s</th>\n<th></th>\n</thead>\n"%(cat_buttons, category_indent, category.get_name())
        out += content
        out += "</table>"
        return out

    def gen_doc_config(self, config, show_all):
        """ Generate the row of a table for a config """
        if (config.is_static()):
            return ''

        if (show_all is False) and (config.is_supported(static_only=True) is False):
            return ''

        return "<tr class=\"config_row\">\n<td>%s</td>\n<td>%s</td>\n</tr>\n"%(config.get_name(), self.gen_doc_config_description(config, show_all))

    def gen_doc_config_description(self, config, show_all):
        """ Generate the description for a config """

        description=''

        # help
        if (config.get_help() is not None):
            description += config.get_help().replace('\n', '<br/>\n') + '<br/><br/>\n'

        description+=self.gen_config_type_description(config)

        description+=self.gen_config_depends_description(config)

        if (config.is_static() is True):
            description+="Static: True<br/>\n"
        
        if (config.has_default() is True):
            description+=self.gen_config_default_description(config)

        if (config.has_options() is True):
            description+=self.gen_config_option_description(config, show_all)

        return description

    def config_pwd_list(self, category):
        """ List the parents of a category up to the root """

        if (category.get_parent() is None):
            return [category.get_name()]
        else:
            return self.config_pwd_list(category.get_parent()) + [category.get_name()]

    def gen_config_type_description(self, config):
        """ Generate config type description """

        if (config.get_type() == None):
            return ''
        elif (config.get_type() == 'single_choice'):
            return 'Type: Single choice from Options<br/>\n'
        elif (config.get_type() == 'int'):
            ret = 'Type: Integer<br/>\n'
            if (config.get_min() is not None):
                ret += 'Minimum value: %s<br/>\n'%config.get_min()
            if (config.get_max() is not None):
                ret += 'Maximum value: %s<br/>\n'%config.get_max()
            return ret
        else:
            return 'Type: %s<br/>\n'%(config.get_type())

    def gen_config_depends_description(self, config):
        """ Generate config dependency description """

        depends = config.get_depends()
        if (depends is None):
            return ""

        depends = EvalExpressions.evaluate(depends, LibConfig().get_config_dict(), static_only=True)
 
        description ='Depends:<br/>\n'
        depends = str(depends).replace("@","")
        description+='%s<br/><br/>\n' % (depends)
        return description

    def gen_config_default_description(self, config):
        """ Generate config default description """
        default_lines=[]

        default_list = config.list_defaults()
        for default in default_list:
            default_value = default.get_value()
            default_depends = default.get_depends()
            
            if default_depends is None:
                msg = "%s<br/>"%default_value
            else:
                msg = "%s if '%s'"%(default_value, default_depends)
            default_lines.append(msg)
            
        if (len(default_lines) == 1):
            description = "Default: %s" % default_lines[0]
        else:
            description = "Defaults:<br/>\n"
            for default_line in default_lines:
                description += "%s<br/>\n" % default_line

        description = description.replace("@","")
        return description

    def gen_config_option_description(self, config, show_all):
        """ Generate config option description """

        if (show_all is True):
            list_options = config.list_options()
        else:
            list_options = []
            for option in config.list_options():
                if option.is_supported(static_only=True) is True:
                    list_options.append(option)

        description ='<br/>Options:<br/>\n'
        description+='<table class="borderless"><tr><td class="borderless"><ul>\n'
        for option in list_options:
            description+='<li>%s</li>\n'%(option.get_name())
        description+='</ul></td><td class="borderless"><ul style="list-style: none;">\n'
        for option in list_options:
            description+='<li>%s=y</li>\n'%(option.id)
        description+='</ul></td></tr></table>\n'
        return description

    def start_report(self):
        """ Start a HTML file """

        return """
<html>
<head>
<style>
body {
    font-family:sans-serif;
    font-size:1em;
}
table {
    border-collapse:collapse;
    font-size:1em;
    border: 1px solid #5a428c;
    width:100%;
    table-layout: fixed;
}
th, td {
    text-align:left;
    padding:1em;
    border: 1px solid #5a428c;
}
td.row_with_table{
    padding: 0;
}
th {
    background-color:#5a428c;
    color:white;
}
.config_row {
    width:100%;
    table-layout: fixed;
}
th:first-child {
    width: 30%;
}
h2{
    font-family:sans-serif;
    font-size:3em;
    color:#5a428c;
    font-weight:bold;
}

a{
    font-family:sans-serif;
    color:#5a428c;
}

.cat_button_open, .cat_button_close{
    color:white;
}
.borderless{
    border: None;
    padding:0em;
}
table.borderless{
    table-layout: auto;
}

ul{
    margin: 0em 1em 0em 1em;
}

.content{
    margin: auto;
    width:100%;
    max-width:100em;
}

@media print{
    body {
        font-family:sans-serif;
        padding:0em 2em 0em 2em;
        -webkit-print-color-adjust:exact !important;
    }
    tr {
        page-break-inside:avoid;
        page-break-after:auto
    }
    .standalone_graph{
        width:70%;
    }
    table {
        width:100%;
        display:block
        border-collapse:collapse;
        font-size:.7em;
        page-break-inside:auto
        border: 1px solid #5a428c;
    }

    h2 {
        font-family:sans-serif;
        font-size:2em;
        color:#5a428c;
        font-weight:bold;
    }
    .page_button_open, .page_button_close,
    .cat_button_open, .cat_button_close{
        display:none;
    }
}
</style>
<script src="http://ajax.googleapis.com/ajax/libs/jquery/1.3.2/jquery.min.js"></script>
</head>
<body>
<div class=\"content\">"""

    def end_report(self):
        """ end a HTML file """

        return """
<script>
$(function()
{

    $('a.cat_button_open').click(function()
    {
        $(this).closest("table").find("table").find("a.cat_button_open").click();

        $(this).closest("table").find("tr.config_row").show();
        $(this).siblings("a.cat_button_close").show();
        $(this).hide();
    });

    $('a.cat_button_close').click(function()
    {
        $(this).closest("table").find("table").find("a.cat_button_close").click();

        $(this).closest("table").find("tr.config_row").hide();
        $(this).siblings("a.cat_button_open").show();
        $(this).hide();
    });
    
    $('a.page_button_open').click(function()
    {
        $('a.cat_button_open').click()
    });
    
    $('a.page_button_close').click(function()
    {
        $('a.cat_button_close').click()
    });

    $('a.page_button_open').click()
});
</script>
</div>
</body>
</html>"""
