#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: PD release
# Owner: Luyi <yi.lu@axelera.ai>

import os
import sys
import argparse
import hjson
import subprocess
import pathlib
import shutil
import filecmp
from mako.template import Template
from mako.lookup import TemplateLookup

from typing import List, Dict, NoReturn
import logging
from datetime import datetime

parser = argparse.ArgumentParser(
  description="arguments"
)
parser.add_argument(
  "-p", "--proj", type=str, default=""
)

parser.add_argument(
  "-b", "--block", type=str, default=""
)

parser.add_argument(
  "-t", "--relType", type=str, default=""
)

parser.add_argument(
  "-r", "--relDirPath", type=str, default=""
)

parser.add_argument(
    "-rf", "--relFormat", type=str, choices=["hier", "flat"], default="hier"
)

parser.add_argument(
    "-d", "--dft", type=bool, action=argparse.BooleanOptionalAction
)

parser.add_argument(
    "-ca", "--copyAll", type=bool, action=argparse.BooleanOptionalAction
)

args = parser.parse_args()

def getGitRepo():
  return subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()


def git_commit() -> str:
  """Return the current Git commit."""
  return subprocess.run(
    args=[
      "git",
      "--no-pager",
      "log",
      "-n",
      "1",
    ],
    check=True,
    universal_newlines=True,
    stdout=subprocess.PIPE,
  ).stdout.strip()


def git_status() -> str:
  """Return the current git status."""
  return subprocess.run(
    args=[
      "git",
      "--no-pager",
      "status",
    ],
    check=True,
    universal_newlines=True,
    stdout=subprocess.PIPE,
  ).stdout.strip()


def loaded_modules() -> str:
  completed_process = subprocess.run(
    args=[
      "module --no-pager list -l",
    ],
    shell=True,
    check=True,
    universal_newlines=True,
    capture_output=True,
  )
  return completed_process.stderr


class releaseGen:
  gitRepo = ""
  tempLookup: TemplateLookup
  benderData = {}
  project = ""
  relType = "" # block or top
  block = "" # name of the block
  benderLoc = "" # location of target bender yml
  relDirPath: pathlib.Path | None = None # release dir path
  incPath = ""
  rtlPath = ""
  incDir = {} # include files
  defines = {} # defines
  files = {} # all files
  fileMapping = {} # full path file v.s. file name
  fileListPath = ""
  fileListPathFormal = ""
  fileListPathFormalImpl = ""
  timestamp = ""
  dft: bool = False

  def __init__(self, proj, relType, block, relDirPath, timestamp, dft=False):
    self.gitRepo = self._getRepoTop()
    self.tempLookup = TemplateLookup(directories=[f'{self.gitRepo}/hw/scripts/pd_release/templates'])
    self.project = proj
    self.relType = relType
    self.block = block
    if self.relType == "top":
      self.benderLoc = f'{self.gitRepo}/hw/impl/{self.project}/asic/rtl'
    else:
      if dft:
        logging.info("** GENERATING RELEASE WITH DFT **")
        self.benderLoc = f'{self.gitRepo}/hw/impl/{self.project}/blocks/{self.block}/rtl/dft'
      else:
        logging.info("** GENERATING RELEASE WITHOUT DFT **")
        self.benderLoc = f'{self.gitRepo}/hw/impl/{self.project}/blocks/{self.block}/rtl'

    data = self._getBenderData(dft)
    self.benderData = hjson.loads(data)
    if relDirPath:
      self.relDirPath = pathlib.Path(relDirPath)
    else:
      self.relDirPath = pathlib.Path(f'{self.gitRepo}/release')
    self.incPath = pathlib.Path(f'{self.relDirPath.resolve()}/includes')
    self.rtlPath = pathlib.Path(f'{self.relDirPath.resolve()}/rtl')
    self.fileListPath = f'{self.relDirPath.resolve()}/rtl/file_list'
    self.timestamp = timestamp
    self.dft = dft

  def _copyTree(self, dir, dest, ignore):
    shutil.copytree(dir, dest, ignore)

  def _copyFile(self, src, dest):
    shutil.copy(src, dest)

  def _getIncludePath(self, name, idx, dir):
    return f'${{AXVAR_RTL_DIR}}/includes/{name}_{str(idx)}'

  def _getRepoTop(self):
    return getGitRepo()

  def _getBenderData(self, dft=True):
    # Calling `bender update` command before executing any Bender script commands
    # This preemptively updates resolves potential mismatch errors where `Bender.yml`
    # lists a dependency `<dep>`, but `Bender.lock` does not include it.
    subprocess.run(['bender', '-d', self.benderLoc, 'update'],
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()
    bender_opts = ['bender', '-d', self.benderLoc, 'script', 'template_json', '-t', 'rtl', '-t', 'asic', '-t', 'sf5a', '-t', 'synthesis']
    if dft:
      bender_opts.extend(['-t', 'dft'])
    return subprocess.run(bender_opts,
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()


  def prepareDir(self):
    # make release dir and include dir
    if not self.relDirPath.exists():
      self.relDirPath.mkdir()
    else:
      print("%s does exist!"%self.relDirPath.resolve())
      sys.exit(1)
    self.incPath.mkdir()
    self.rtlPath.mkdir()

  def prepareInc(self):
    # copy all include dirs
    if self.benderData["all_incdirs"]:
      for idx in range(len(self.benderData["all_incdirs"])):
        dir = pathlib.Path(self.benderData["all_incdirs"][idx]).resolve()
        name = pathlib.Path(self.benderData["all_incdirs"][idx]).name
        if dir not in self.incDir:
          self.incDir[dir] = self._getIncludePath(name, idx, dir)
          self._copyTree(dir, f'{self.incPath}/{name}_{str(idx)}', ignore=shutil.ignore_patterns("*.yml"))
          # TODO, not must, remove non rtl file from the folder

  def prepareFiles(self):
    # copy all files:
    if self.benderData["all_files"]:
      for idx in range(len(self.benderData["all_files"])):
        file = pathlib.Path(self.benderData["all_files"][idx]).resolve()
        name = pathlib.Path(self.benderData["all_files"][idx]).name
        # Copy all files if copyAll switch is defined
        if args.copyAll or self.gitRepo in str(file):
          if name not in self.files:
            self.files[name] = file
            self._copyFile(file, self.rtlPath.resolve())
            self.fileMapping[file] = name
          else:
            if not filecmp.cmp(file, self.files[name]):
              print("The following files have the same name: %s ; %s"%(file, self.files[name]))
              sys.exit(1)
            else:
              self.fileMapping[file] = name
        else:
          self.fileMapping[file] = name

  def prepareData(self):
    # loop through sources
    if self.benderData["srcs"]:
      for idx in range(len(self.benderData["srcs"])):
        # replace files
        fileList = []
        for file in self.benderData["srcs"][idx]["files"]:
          filePath = pathlib.Path(file).resolve()
          if filePath in self.fileMapping:
            if args.copyAll or self.gitRepo in str(filePath):
              fileList.append(self.fileMapping[filePath])
            else:
              fileList.append(str(filePath))
          else:
            print("The file %s is not in all_file_list"%filePath)
            sys.exit(1)
        self.benderData["srcs"][idx]["files"] = fileList
        # replace inc
        incList = []
        for inc in self.benderData["srcs"][idx]["incdirs"]:
          tempPath = pathlib.Path(inc).resolve()
          if tempPath in self.incDir:
            # filter out repo include paths
            if self.gitRepo not in str(self.incDir[tempPath]):
              logging.info(f"Adding include path: {str(self.incDir[tempPath])}")
              incList.append(self.incDir[tempPath])
            else:
              logging.info(f"Skipping repo include path: {str(self.incDir[tempPath])}")
          else:
            logging.info("The include dir %s is not in all_inc_list"%tempPath)
            sys.exit(1)
        self.benderData["srcs"][idx]["incdirs"] = incList


  def topRender(self):
    cfg = {}
    cfg["srcs"] = self.benderData["srcs"]
    cfg["type"] = ""

    # for synthesis list
    t = Template(f"<%include file='file_list_sh.mako'/>",lookup=self.tempLookup)
    renderedOut = t.render(**cfg)
    with open(self.fileListPath, 'wb') as file:
      file.write(renderedOut.encode())

    # for formality list - reference
    cfg["type"] = "ref"
    t = Template(f"<%include file='file_list_formality.mako'/>",lookup=self.tempLookup)
    renderedOut = t.render(**cfg)
    with open(self.fileListPathFormal, 'wb') as file:
      file.write(renderedOut.encode())

    # for formality list - reference
    cfg["type"] = "impl"
    t = Template(f"<%include file='file_list_formality.mako'/>",lookup=self.tempLookup)
    renderedOut = t.render(**cfg)
    with open(self.fileListPathFormalImpl, 'wb') as file:
      file.write(renderedOut.encode())

  def finishRelease(self):
    # Do release cleanup here
    pass

  def release_manifest(
    self
  ) -> None:
    manifest_file = self.relDirPath / "release_manifest.md"
    t = self.tempLookup.get_template("release_manifest.mako")
    output = t.render(
      block_name=self.block,
      timestamp=self.timestamp,
      dft=self.dft,
      git_commit=git_commit(),
      git_status=git_status(),
      loaded_modules=loaded_modules(),
    )
    with manifest_file.open("wb") as file:
       file.write(output.encode())



logging.basicConfig(level=logging.INFO)

class FlatReleaseGen(releaseGen):
    def __init__(self, proj: str, relType: str, block: str, relDirPath: str, timestamp: str, dft: bool = True):
        """
        Initializes a new instance of FlatReleaseGen that generates a flat release

        :param proj: Name of the project.
        :param relType: Type of release.
        :param block: Name of the block within the project.
        :param relDirPath: Optional path to the release directory. If None, uses default path.
        """
        super().__init__(proj, relType, block, None, timestamp,dft)
        self.benderData = hjson.loads(self._getBenderData(dft))
        if relDirPath:
          self.relDirPath = pathlib.Path(relDirPath)
        else:
          self.relDirPath = pathlib.Path(f'{self.gitRepo}/release')

    def _copyFile(self, src: pathlib.Path, dest: pathlib.Path):
        """
        Copies a file from src to the directory specified by dest.

        :param src: Source file path.
        :param dest: Destination file name within the release directory.
        """
        try:
            dest_path = self.relDirPath / src.name
            if dest_path.exists():
              if not filecmp.cmp(src, dest_path, shallow=False):
                raise FileExistsError(f"Error copying Source file. \
                Destination file '{dest_path}' already exists and is different than {src}.")
              else:
                return
            logging.info(f"Copying file '{src}' to '{dest_path}'")
            shutil.copy(src, dest_path)
            os.chmod(dest_path, 0o444)  # Set file as read-only
        except Exception as e:
            logging.error(f"Failed to copy from '{src}' to '{dest_path}': {e}")
            raise e

    def _copyTree(self, dir: str, dest: pathlib.Path, ignore=None):
        """
        Recursively copies a directory tree from 'dir' to 'dest', ignoring files specified.

        :param dir: Directory to copy from.
        :param dest: Destination directory path.
        :param ignore: List of patterns to ignore.
        """
        try:
            dir_path = pathlib.Path(dir)
            if self.gitRepo not in str(dir_path):
              logging.info(f"Skip Copying Non-Repo include path '{dir_path}'")
              return
            logging.info(f"Copying Repo include path '{dir_path}'")
            for item in dir_path.iterdir():
                if item.is_file():
                    if ignore and ignore(dir_path, [item.name]):
                        continue
                    dest_path = self.relDirPath / pathlib.Path(item.name)
                    # check if file with same name exists
                    # also match the contents, if they dont then raise error and exit
                    if dest_path.exists():
                      if not filecmp.cmp(item, dest_path, shallow=False):
                        raise FileExistsError(f"Error copying include file. \
                          Destination file '{dest_path}' already exists and is different than {item}.")
                      else:
                        continue
                    logging.info(f"Copying file '{item}' to '{dest_path}'")
                    shutil.copy(item, dest_path)
                    os.chmod(dest_path, 0o444)
                elif item.is_dir():
                    self._copyTree(item, dest, ignore)
        except Exception as e:
            logging.error(f"An error occurred while copying tree '{dir}': {e}")
            raise e

    def _getIncludePath(self, name, idx, dir):
      return dir

    def _copyConstraintsDirectory(self):
        # Define the path for the constraints directory based on the block
        constraints_dir = pathlib.Path(f"{self.gitRepo}/hw/impl/europa/blocks/{self.block}/synth-rtla/constraints")

        # Define the destination directory path
        dest_dir = self.relDirPath / constraints_dir.name

        # Check if the constraints directory exists
        if constraints_dir.exists():
            try:
                # Copy the entire directory
                shutil.copytree(constraints_dir, dest_dir)
                logging.info(f"Successfully copied constraints directory to: {dest_dir}")
            except Exception as e:
                logging.error(f"Error copying constraints directory: {e}")
                raise e
        else:
            logging.warning(f"Constraints directory does not exist: {constraints_dir}")

    def prepareDir(self):
        """
        Prepares the directory for the release, creating necessary subdirectories
        and handling timestamping.
        """
        try:
            self.ip_dir = self.relDirPath / self.block
            self.ip_dir.mkdir(parents=True, exist_ok=True)
            self.relDirPath = self.ip_dir / self.timestamp

            if self.relDirPath.exists():
              error_str = f"Release directory '{self.relDirPath}' already exists!"
              logging.error(error_str)
              raise FileExistsError(error_str)

            self.relDirPath.mkdir()
            block_name_suffix = ""
            if self.relType != "top":
              block_name_suffix = "_p"

            block_name = pathlib.Path(self.block).parts[-1]  # Get the last part of the block path
            self.fileListPath = self.relDirPath / f"{block_name}{block_name_suffix}.read_rtl.tcl"
            self.fileListPathFormal = self.relDirPath / f"{block_name}{block_name_suffix}.read_rtl_formality.tcl"
            self.fileListPathFormalImpl = self.relDirPath / f"{block_name}{block_name_suffix}.read_rtl_formality_impl.tcl"

        except Exception as e:
            logging.error(f"An error occurred while preparing directory: {e}")
            raise e

    def finishRelease(self):
      # copy constraints
      self._copyConstraintsDirectory()
      # finished copying, make directories read-only
      os.chmod(self.relDirPath, 0o555)


def process_block(proj: str, relType: str, block: str, relDirPath: str, relFormat: str, timestamp: str, dft: bool = True) -> NoReturn:
    """
    Processes the release generation for a given block.

    Args:
        proj (str): The project identifier.
        relType (str): The type of release.
        block (str): The block to generate for.
        relDirPath (str): The path to the directory where the release files will be stored.
        relFormat (str): The format of the release, such as 'hier' for hierarchical or 'flat' for flat.
    """

    logging.info(f"** STARTING RELEASE GENERATION FOR '{block}' at: {relDirPath}/{block}/{timestamp}")

    if relFormat == "hier":
        release = releaseGen(proj, relType, block, relDirPath, timestamp, dft)
    else:
        release = FlatReleaseGen(proj, relType, block, relDirPath, timestamp, dft)

    try:
        release.prepareDir()
        release.prepareInc()
        release.prepareFiles()
        release.prepareData()
        release.topRender()
        logging.info(f"** RELEASE GENERATED: {relDirPath}/{block}/{timestamp}\n")
    finally:
        release.release_manifest()
        release.finishRelease()


def main():
  proj = args.proj
  block = args.block
  relType = args.relType
  relDirPath = args.relDirPath
  relFormat = args.relFormat
  timestamp = datetime.now().strftime("%Y%m%d%H%M")

  if block == "all":
      git_repo = getGitRepo()
      #TODO: do away with block_folder_paths and add a fn that would decide/enlist(based on a heuristic/config) if a dir is eligible for release
      block_folder_paths = [
          f"{git_repo}/hw/impl/europa/blocks/",
          f"{git_repo}/hw/impl/europa/blocks/noc"
      ]
      for block_folder in block_folder_paths:
          directory_entries = os.listdir(block_folder)
          blocks = [entry for entry in directory_entries if os.path.isdir(os.path.join(block_folder, entry))]
          for each_block in blocks:
              try:
                  # Determine the relative path prefix based on the block folder path
                  relative_path_prefix = os.path.relpath(block_folder, git_repo + "/hw/impl/europa/blocks")
                  if relative_path_prefix != ".":
                      block_name = os.path.join(relative_path_prefix, each_block)
                  else:
                      block_name = each_block

                  # Call process_block with the modified block name
                  process_block(proj, relType, block_name, relDirPath, relFormat, timestamp, args.dft)
              except Exception as e:
                  logging.error(f"RELEASE GENERATION FAILED FOR BLOCK:{each_block} ERROR: {e}")

  else:
      process_block(proj, relType, block, relDirPath, relFormat, timestamp, args.dft)

if __name__ == "__main__":
  main()
