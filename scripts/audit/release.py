#!/usr/bin/env python3

import argparse
import calendar
import os
import pathlib
import shutil
import logging
import stat

logger = logging.getLogger(__name__)

def make_read_only(path: pathlib.Path) -> None:
    for item in path.iterdir():
        if item.is_file():
            item.chmod(0o444)
        elif item.is_dir():
            make_read_only(item)

    path.chmod(0o555)


def main():

  parser = argparse.ArgumentParser(
                    prog='certificate release',
                    description='Create a release area based on ceritficate',
                    epilog='Please refer to the flow documentation for use of this tool.')

  parser.add_argument(
    '-c',
    '--certificate',
    required = True,
    type=pathlib.Path,
    help = "Certificate File",
  )

  logging.basicConfig(
    level=logging.INFO,
    format='%(levelname)s: %(message)s',
  )

  args = parser.parse_args()

  # Read the certificate file and parse it to retrieve data.
  f_ptr = open(args.certificate, 'r')

  logging.info(f"Reading Certificate File: {args.certificate}")
  lines = f_ptr.readlines()

  # Parse Certificate for details
  for l in lines:
    la = [a.strip() for a in l.split(":", maxsplit=1)]
    if la[0] == "BLOCK":
      blk = la[1].lower()
    elif la[0] == "DATE":
      date_array = la[1].split(" ")
      date = f"{date_array[5]}{list(calendar.month_abbr).index(date_array[1]):02}{date_array[2]:02}_{date_array[3].replace(':', '')}"
    elif la[0] == "MILESTONE":
      milestone = la[1].lower()

  logging.info(f" >> Block             : {blk}")
  logging.info(f" >> Date              : {date}")
  logging.info(f" >> Milestone         : {milestone}")

  # Create Release Directory. If it exists, delete it to clean it out.
  base_release_dir = pathlib.Path("/data/releases/europa/LD_CERTIFICATES_EUROPA")
  release_dir = base_release_dir / milestone / blk / date
  logging.info(f" >> Release Directory : {release_dir}")
  if release_dir.exists():
    logging.info("Release Directory Exists: Removing it")
    shutil.rmtree(release_dir)
  logging.info(f"Creating Release Directory: {str(release_dir)}")
  for parent in reversed(release_dir.parents):
    if not parent.exists():
      parent.mkdir(exist_ok=True)
      os.chmod(parent, 0o775)

  # Now copy the directories under audit_reports (alongside cetificate.txt)
  for certdir in ["audit_reports"]:
    logdirs = args.certificate.parent.absolute() / certdir
    for d in [ f.path for f in os.scandir(logdirs) if f.is_dir() ]:
      logging.info(f"Copying Logs: {d}")
      shutil.copytree(d, os.path.join(release_dir, d.split("/")[-1]))
  shutil.copytree(
    src=args.certificate.parent.absolute() / "audit_signoffs",
    dst=release_dir / "signoff_files",
  )
  # Finally copy the certificate
  shutil.copyfile(
    src=args.certificate,
    dst=release_dir / args.certificate.name,
  )

  # Finally make the release read only
  make_read_only(release_dir)

if __name__ == '__main__':
  main()
