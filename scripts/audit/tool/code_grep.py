import re
import tool.signoff_codes

def define_error_message_search (milestone):
  if milestone == "gold":
    # All lines reported in the todo/waive/... report are considered errors at gold.
    error_list = [re.compile(".+")]
  else:
    # All lines reported in the todo/waive/... report are warnings at bronze or silver.
    error_list = []
  return error_list


def define_warning_message_search (milestone):
  if milestone == "gold":
    warning_list = []
  else:
    # All lines reported in the todo/waive/... report are warnings at bronze or silver.
    warning_list = [re.compile(".+")]
  return warning_list

def errors_allowed (milestone):
  return milestone == "skeleton"

def warnings_allowed (milestone):
  return milestone in ["skeleton", "prebronze", "bronze"]


def find_rtl_codes ():
  tool_codes = {}
  for c in tool.signoff_codes.codes:
    tool_codes[c] = []
    try: 
      tool_codes[c].extend(tool.signoff_codes.codes[c]['code_grep'])
    except KeyError:
      pass
  return tool_codes

