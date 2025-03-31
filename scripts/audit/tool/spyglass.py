import re
import tool.signoff_codes

grep_str: list[str] = ["FATAL MESSAGES","Fatal","Error","Warning"]

def define_error_message_search (milestone):
  error_list = [re.compile(".*FATAL MESSAGES.*"),
                re.compile(".*Fatal.*"),
                re.compile(".*Error.*")]
  return error_list


def define_warning_message_search (milestone):
  warning_list = [re.compile(".*Warning.*")]
  return warning_list

def errors_allowed (milestone):
  return False

def warnings_allowed (milestone):
  return milestone in ["skeleton", "prebronze", "bronze"]

def find_rtl_codes ():
  tool_codes = {}
  for c in tool.signoff_codes.codes:
    tool_codes[c] = []
    try: 
      tool_codes[c].extend(tool.signoff_codes.codes[c]['spyglass'])
    except KeyError:
      pass
  return tool_codes

