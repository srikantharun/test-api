#!/usr/bin/env python3

import argparse
import importlib
import logging
import os
import re
import subprocess
import sys

logger = logging.getLogger(__name__)

class message_item():
  '''
  '''

  def __init__ (self, message, logfile, linenumber):

    self.message = message.strip()
    self.file = logfile
    self.line = linenumber

    self.signoff   = None

  def __str__(self):
    return f"Msg {self.file.filename}[{self.line}] : {self.message}"

  def add_signoff(self, signoff, iserror):
    self.signoff = signoff
    logger.debug(f"Matched: Signoff ({signoff.filename},{signoff.line}) against message ({self.file.filename},{self.line})")
    if iserror:
      self.file.errors_so += 1
    else:
      self.file.warnings_so += 1

  def explain_signoff(self):
    if self.signoff:
      return (f"Line {self.line}: ({self.message}) => SIGNED BY {self.signoff.filename},{self.signoff.line}: ({self.signoff.regexp_raw})\n")
    return ""

  def list_unsignedoff(self):
    if not self.signoff:
      return (f"Line {self.line}: ({self.message})\n")
    return ""

class logfile ():
  '''
  '''
  def __init__(self, filename, tool, milestone, quiet, condense=True):
    self.error_search = []
    self.warning_search = []
    self.filename = filename
    self.tool = tool
    self.milestone = milestone
    self.error_list = []
    self.warning_list = []
    self.errors_so = 0
    self.warnings_so = 0
    self.quiet = quiet

    logger.info(f"Audit Tool Analyzing {self.tool} Logfile with {self.milestone} milestone configuration.")

    self.tooldefs = importlib.import_module(f"tool.{self.tool}")
    self.error_search.extend(self.tooldefs.define_error_message_search(self.milestone))
    self.warning_search.extend(self.tooldefs.define_warning_message_search(self.milestone))
    self.read_logfile(condense)


  def read_logfile(self, condense):
    logger.info(f"Reading Logfile: {self.filename}")

    try:
      if (condense and hasattr(self.tooldefs, "grep_str")):
        idx=0
        lfp = []
        for g in self.tooldefs.grep_str:
          cmd = f"egrep \"{g}\" {self.filename} > {self.filename}.cds{idx}"
          os.system(cmd)
          lfp.append(open(f"{self.filename}.cds{idx}", 'r'))
          idx += 1
      else:
        lfp = open(self.filename, 'r')
    except FileNotFoundError:
      if self.quiet:
        logger.setLevel(logging.INFO)
        logger.info(f"[FAIL] {self.tool.upper():6} : {self.milestone.upper()} : MISSING {self.filename}")
      else:
        logger.fatal(f"Missing Log File: {self.filename}")
      sys.exit(1)

    all_searches = self.error_search + self.warning_search
    try:
      for i in range(len(lfp)):
        iserror = i < len(self.error_search)
        lfd = lfp[i].read()
        self.process_file(lfd, [all_searches[i]],int(iserror))

    except TypeError:
      lfd = lfp.read()
      self.process_file(lfd, all_searches, len(self.error_search))


  def process_file(self, lfd, all_searches, n_error_searches):
    lines = 1
    while len(lfd) > 0 and not lfd.isspace():
      # Initial Searches
      s_res = [x.search(lfd) for x in all_searches]
      first_idx = None
      for i in range(len(s_res)):
        if first_idx == None and s_res[i] != None:
          first_idx = i
        elif s_res[i] != None:
            if s_res[first_idx].start() > s_res[i].start():
              first_idx = i

      if first_idx != None:
        lines += lfd[0:s_res[first_idx].start()].count("\n")
        if first_idx < n_error_searches:
          # Error
          self.error_list.append(message_item(s_res[first_idx].group(0), self, lines))
        else:
          self.warning_list.append(message_item(s_res[first_idx].group(0), self, lines))
        lfd = lfd[s_res[first_idx].end():]
      else:
        lfd = ""
        logger.info("Processing Done")

  def summarise(self):
    errors_remain = len(self.error_list) - self.errors_so
    warnings_remain = len(self.warning_list) - self.warnings_so
    min_offset = 8
    if len(self.filename) < min_offset:
      fileins = (min_offset-len(self.filename)) * " "
      reptins = ""
    else:
      fileins = ""
      reptins = (len(self.filename) - min_offset) * " "
    table_sep = "=" * (len(self.filename) + 28)
    table_sep_minor = "-" * (len(self.filename) + 28)
    logger.info(table_sep)
    logger.info(f"{self.filename}{fileins}   |    Raw    | w/Signoff |")
    logger.info(table_sep_minor)
    logger.info(f"{reptins}Errors     |  {len(self.error_list):7d}  |  {errors_remain:7d}  |")
    logger.info(f"{reptins}Warnings   |  {len(self.warning_list):7d}  |  {warnings_remain:7d}  |")
    logger.info(table_sep)
    remaining = 0
    if not self.tooldefs.errors_allowed(self.milestone):
      remaining += errors_remain
    if not self.tooldefs.warnings_allowed(self.milestone):
      remaining += warnings_remain
    return remaining

  def dump_logs(self, fname_base=None ):
    explained_signoff = f"Signed Off Messages for logfile: {self.filename}\n\n"
    no_signoff = f"Non-Signed Off Messages for logfile: {self.filename}\n\n"
    explained_signoff += "####################################\n"
    explained_signoff += "# ERROR MESSAGES                   #\n"
    explained_signoff += "####################################\n\n"
    no_signoff += "####################################\n"
    no_signoff += "# ERROR MESSAGES                   #\n"
    no_signoff += "####################################\n\n"
    for message in self.error_list:
      explained_signoff += message.explain_signoff()
      no_signoff += message.list_unsignedoff()
    explained_signoff += "\n####################################\n"
    explained_signoff += "# WARNING MESSAGES                 #\n"
    explained_signoff += "####################################\n\n"
    no_signoff += "\n####################################\n"
    no_signoff += "# WARNING MESSAGES                 #\n"
    no_signoff += "####################################\n\n"
    for message in self.warning_list:
      explained_signoff += message.explain_signoff()
      no_signoff += message.list_unsignedoff()
    if not fname_base:
      fname_base = self.filename
    f_ptr = open(fname_base + ".signedoff.rpt", 'w')
    f_ptr.write(explained_signoff)
    f_ptr.close()
    f_ptr = open(fname_base + ".notsignedoff.rpt", 'w')
    f_ptr.write(no_signoff)
    f_ptr.close()

class signoff():

  def __init__(self, regexp, filename, line, comment):
    #print("Creating Signoff: %s" % comment)
    self.regexp = re.compile(regexp)
    self.regexp_raw = regexp
    self.filename = filename
    self.line = line
    self.comment = comment

    self.signoffs = []


  def report_unmatched (self, ptr):
    ptr.write(f"{self.filename}[{self.line}]: {self.regexp.pattern} : {len(self.signoffs)}\n")



in_comment = "(?:\/\*.+?\*\/)" # /* text */
norm_comment = "(?:\/\/[^\n]*\n)" # // text ending with newline
macro = "(?:`\w+(?:\s*\(.*?\))?|`\w+\s+\w+)" # support `bla | `bla(cookie) | `bla cookie
comment = f"(?:{in_comment}|{norm_comment})" # either inline or normal one
port = "(?:\.[\*\w]+\s*(?:\([\w\W]*?\))?)" # .* | .text | .text(bla)
inst_name="\w+\s*(?:\[[\w\-\:\+]+\])?" # inst optionally followed by instance array [something : down]
regex_mod_inst = f"\n\s*(\w+)\s+\
(?:#\s*\(({macro}|{port}\s*{comment}?|{comment}|(?:\w+(?:\'\w*)?)|\(.*?\)|[\-\+,:\s])+\))?\
\s*{comment}?\s*({inst_name})[\s\n]*\(\
({macro}|{port}\s*{comment}?|{comment}|[,\s])*\
\s*\);"

# print(regex_mod_inst)
re_signoff     = re.compile("^ASO:\s*(.*)\s*\[(.*)\]\s*regexp=\"(.*)\"")
re_rtl_signoff = re.compile("(.*)\/\/\s*ASO\-([0-9A-Z_,]+)(|\(.*\))\s*:(.*)")
re_instance    = re.compile(regex_mod_inst, re.MULTILINE )
re_port_in_line = re.compile("\.(\w+)")

def read_signoff_file(filename, tool):
  signoffs = []

  logger.info(f"Reading Signoff file: {filename}, filtering for {tool}")
  f_ptr = open(filename, 'r')
  linenum = 0
  line = ""
  for l in f_ptr.readlines():
    linenum += 1
    if l.startswith('#'):
      if len(line) != 0:
        logger.error(f"Error: Malformed Signoff ({filename},{linenum}):")
        logger.error(f"   >>> {line}")
    else:
      line += l.strip()
      signoff_re_match = re_signoff.match(line)
      if signoff_re_match:
        if signoff_re_match.group(2) == tool:
          logger.debug(f"Signoff added from ({filename},{linenum})")
          signoffs.append(signoff(signoff_re_match.group(3), filename, linenum, signoff_re_match.group(1)))
        line = ""
  f_ptr.close()
  logger.info(f"  {len(signoffs)} Signoffs Found")
  return signoffs

def is_in_instance(all_inst, line_nr):
    def_inst=dict()
    def_inst["mod_name"]       = 0
    def_inst["inst_name"]      = 0
    def_inst["inst_name_line"] = 0
    def_inst["inst_st_line"]   = 0
    def_inst["inst_end_line"]  = 0
    inst = next((inst for inst in all_inst if inst["inst_st_line"] <= line_nr and inst["inst_end_line"] >= line_nr), def_inst)
    return inst

def get_all_instances(rtl):
    # search all instances and get there start and end line number:
    m_rtl=rtl
    instance = re_instance.search(m_rtl)
    m_start_line = 1
    all_inst=[]
    while instance:
        inst=dict()
        inst_name_line = m_start_line + m_rtl[0:instance.start(3)].count("\n")
        inst_st_line   = m_start_line + m_rtl[0:instance.end(1)].count("\n")
        inst_end_line  = m_start_line + m_rtl[0:instance.end(0)].count("\n")
        inst["mod_name"]       = instance.group(1)
        inst["inst_name"]      = instance.group(3)
        inst["inst_name_line"] = inst_name_line
        inst["inst_st_line"]   = inst_st_line
        inst["inst_end_line"]  = inst_end_line
        all_inst.append(inst)

        m_rtl=m_rtl[instance.end():]
        m_start_line = inst_end_line
        instance=re_instance.search(m_rtl)
        logging.debug(f"Found instance {inst}")
    return all_inst

def read_rtl_signoffs(rtl, extra_targets, tool, lf, signoff_exclude):
  signoffs = []
  code = lf.tooldefs.find_rtl_codes()
  logger.info(f"Reading Signoffs from RTL codebase.")
  if rtl:
    # parse all bender targets, required rtl and extra if provided:
    bender_array = ['bender', 'script', 'flist', '-t', 'rtl', '-d', rtl]
    for t in extra_targets.split():
        bender_array.append('-t')
        bender_array.append(t)
    result = subprocess.run(bender_array, stdout=subprocess.PIPE)
    for flist_item in (result.stdout.decode('utf-8').split('\n')):
      if not flist_item.startswith("+incdir+") and len(flist_item) > 1 and not any(flist_item.startswith(excl_path) for excl_path in signoff_exclude):
        start_line = 1
        logger.debug(f"Reading RTL file: {flist_item}")
        f_ptr = open(flist_item)
        rtl = f_ptr.read()
        f_ptr.close()
        rtl_signoff = re_rtl_signoff.search(rtl)
        all_inst = get_all_instances(rtl)

        # print(rtl_signoff)
        while rtl_signoff:
          line_delta = int(rtl_signoff.group(1).isspace())
          if rtl_signoff.group(3):
            try:
              line_delta = int(rtl_signoff.group(3)[1:-1])
            except TypeError:
              logging.error(f"Unexpected Line Delta ({flist_item}, {start_line})")
          signoff_line = start_line + rtl[0:rtl_signoff.start(2)].count("\n") + line_delta
          in_inst=is_in_instance(all_inst, signoff_line) # get instance, if applicable, of current line
          logging.debug(f"Found Signoff {rtl_signoff.group(2)} in {flist_item},{signoff_line}")
          for c in rtl_signoff.group(2).split(","):
            if c in code:
              for regexp in code[c]:
                repl_dict_base={'file': flist_item, 'line' : signoff_line}
                repl_dict_base = repl_dict_base | in_inst
                ports=re_port_in_line.findall(rtl_signoff.group(1))
                if len(ports)<1:
                  ports.append("NO_PORT")
                for port in ports:
                  repl_dict=repl_dict_base | {"port":port}
                  signoffs.append(signoff(regexp % repl_dict, flist_item, signoff_line, rtl_signoff.group(4)))
          rtl = rtl[rtl_signoff.end():]
          start_line = signoff_line
          rtl_signoff = re_rtl_signoff.search(rtl)
  logger.info(f"  {len(signoffs)} Signoffs Found")
  return signoffs

def match_engine (signoff, message_list, iserror):
  for message in message_list:
    if not message.signoff:
      match = signoff.regexp.match(message.message)
      if match:
        message.add_signoff(signoff, iserror)
        signoff.signoffs.append(message)

def main():

  parser = argparse.ArgumentParser(
                    prog='audit_signoff',
                    description='Provide a generic mechanism to waive / signoff messages from tools.',
                    epilog='Please refer to the flow documentation for use of this tool.')

  parser.add_argument(
    '-t',
    '--tool',
    required = True,
    choices = ['code_grep', 'questa', 'rtla', 'spyglass'],
    help = "Set the tool to signoff, this selects an error/warning identifier as well as reducing the signoffs to process.",
  )
  parser.add_argument(
    '-l',
    '--logfile',
    required = True,
    action='store',
    help="Logfile to search for errors/warnings from.",
  )
  parser.add_argument(
    '-o',
    '--outfile_base',
    action='store',
    default=None,
    help="Output logfile base names (default is incoming logfile)",
  )
  parser.add_argument(
    '-s',
    '--signofffile',
    action='append',
    default=[],
    help="Axelera Signoff File (.aso) to use for signoffs.",
  )
  parser.add_argument(
    '-r',
    '--rtl',
    action='store',
    default=None,
    help="Apply RTL signoffs, Bender directory for files.",
  )
  parser.add_argument(
    '-e',
    '--extra_targets',
    action='store',
    default="",
    help="Apply RTL signoffs, Extra Bender targets (for example dft).",
  )
  parser.add_argument(
    '-q',
    '--quiet',
    action='store_true',
    help="Used for cerification 1 line summary.",
  )
  parser.add_argument(
    '-w',
    '--raw',
    action='store_true',
    help="Dont condense (process raw) log files"
  )
  parser.add_argument(
    '-d',
    '--debug',
    action='store_true',
    help="Used for additional logging",
  )
  parser.add_argument(
    '-m',
    '--milestone',
    action='store',
    default='gold',
    choices=['skeleton', 'prebronze', 'bronze', 'silver', 'gold'],
    help="Will adjust the warning / error set for audit",
  )
  parser.add_argument(
    '--log-output',
    default="audit_run.log",
    help="Set output log file.",
  )

  args = parser.parse_args()

  if args.debug:
    log_level = logging.DEBUG
  elif args.quiet:
    log_level = logging.WARNING
  else:
    log_level = logging.INFO

  signoff_exclude_path = os.path.expandvars('$REPO_ROOT/scripts/audit/signoff_exclude.list')

  logging.basicConfig(
    level=log_level,
    format='%(levelname)s: %(message)s',
    handlers=[
      logging.FileHandler(args.log_output),
      logging.StreamHandler()
    ]
  )
  logger.setLevel(log_level)

  signoffs = []


  with open(signoff_exclude_path, 'r') as file:
    signoff_exclude = [os.path.expandvars(line.strip()) for line in file]

  # Read Log File
  lf = logfile(args.logfile, args.tool, args.milestone, quiet=args.quiet, condense=not(args.raw))

  # Read Standalone Signoff Files
  for s in args.signofffile:
    signoffs.extend(read_signoff_file(s, args.tool))

  # Read Signoffs from RTL
  signoffs.extend(read_rtl_signoffs(args.rtl, args.extra_targets, args.tool, lf, signoff_exclude))

  # Run Signoff
  logger.info("Matching...")
  for signoff in signoffs:
    match_engine(signoff, lf.error_list, iserror=True)
    match_engine(signoff, lf.warning_list, iserror=False)

  # Dump Log Files
  lf.dump_logs(args.outfile_base)

  ptr = open(args.outfile_base +  ".unmatched_signoffs.log", "w")
  for signoff in signoffs:
    signoff.report_unmatched(ptr)

  # Report Results
  remaining = lf.summarise()
  result = "FAIL"
  if remaining == 0:
    result = "PASS"
  logger.info(f"[{result}] Audit has {result}ED for {args.milestone.upper()} certification.")
  if args.quiet:
    logger.setLevel(logging.INFO)
    logger.info(f"[{result}] {args.tool.upper():9} : {args.milestone.upper()} : {lf.filename}")
  sys.exit(remaining)





if __name__ == '__main__':
  main()
