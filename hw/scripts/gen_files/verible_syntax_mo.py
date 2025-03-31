#!/usr/bin/env python3

# Copyright 2017-2020 The Verible Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Wrapper for ``verible-verilog-syntax --export_json``"""

import argparse
import collections
import json
import hjson
import logging
import re
import pathlib
import pprint
import subprocess
import sys
from typing import Any, Callable, Dict, Iterable, List, Optional, Union

import anytree
import dataclasses
from types import SimpleNamespace

_CSI_SEQUENCE = re.compile("\033\\[.*?m")


def _colorize(formats: List[str], strings: List[str]) -> str:
    result = ""
    fi = 0
    for s in strings:
        result += f"\033[{formats[fi]}m{s}\033[0m"
        fi = (fi + 1) % len(formats)
    return result


# Type aliases

CallableFilter = Callable[["Node"], bool]
KeyValueFilter = Dict[str, Union[str, List[str]]]
TreeIterator = Union["_TreeIteratorBase", anytree.iterators.AbstractIter]

# Custom tree iterators with an option for reverse children iteration


class _TreeIteratorBase:
    def __init__(
        self,
        tree: "Node",
        filter_: Optional[CallableFilter] = None,
        reverse_children: bool = False,
    ):
        self.tree = tree
        self.reverse_children = reverse_children
        self.filter_ = filter_ if filter_ else lambda n: True

    def __iter__(self) -> Iterable["Node"]:
        yield from self._iter_tree(self.tree)

    def _iter_children(self, tree: Optional["Node"]) -> Iterable["Node"]:
        if not tree or not hasattr(tree, "children"):
            return []
        return tree.children if not self.reverse_children else reversed(tree.children)

    def _iter_tree(self, tree: Optional["Node"]) -> Iterable["Node"]:
        raise NotImplementedError("Subclass must implement '_iter_tree' method")


class PreOrderTreeIterator(_TreeIteratorBase):
    def _iter_tree(self, tree: Optional["Node"]) -> Iterable["Node"]:
        if self.filter_(tree):
            yield tree
        for child in self._iter_children(tree):
            yield from self._iter_tree(child)


class PostOrderTreeIterator(_TreeIteratorBase):
    def _iter_tree(self, tree: Optional["Node"]) -> Iterable["Node"]:
        for child in self._iter_children(tree):
            yield from self._iter_tree(child)
        if self.filter_(tree):
            yield tree


class LevelOrderTreeIterator(_TreeIteratorBase):
    def _iter_tree(self, tree: Optional["Node"]) -> Iterable["Node"]:
        queue = collections.deque([tree])
        while len(queue) > 0:
            n = queue.popleft()
            if self.filter_(n):
                yield n
            queue.extend(self._iter_children(n))


class Node(anytree.NodeMixin):
    """Base VeribleVerilogSyntax syntax tree node.

    Attributes:
      parent (Optional[Node]): Parent node.
    """

    def __init__(self, parent: Optional["Node"] = None):
        self.parent = parent

    @property
    def syntax_data(self) -> Optional["SyntaxData"]:
        """Parent SyntaxData"""
        return self.parent.syntax_data if self.parent else None

    @property
    def start(self) -> Optional[int]:
        """Byte offset of node's first character in source text"""
        raise NotImplementedError("Subclass must implement 'start' property")

    @property
    def end(self) -> Optional[int]:
        """Byte offset of a character just past the node in source text."""
        raise NotImplementedError("Subclass must implement 'end' property")

    @property
    def text(self) -> str:
        """Source code fragment spanning all tokens in a node."""
        start = self.start
        end = self.end
        sd = self.syntax_data
        if (
            (start is not None)
            and (end is not None)
            and sd
            and sd.source_code
            and end <= len(sd.source_code)
        ):
            return sd.source_code[start:end].decode("utf-8")
        return ""

    def __repr__(self) -> str:
        return _CSI_SEQUENCE.sub("", self.to_formatted_string())

    def to_formatted_string(self) -> str:
        """Print node representation formatted for printing in terminal."""
        return super().__repr__()


class BranchNode(Node):
    """Syntax tree branch node

    Attributes:
      tag (str): Node tag.
      children (Optional[Node]): Child nodes.
    """

    def __init__(
        self,
        tag: str,
        parent: Optional[Node] = None,
        children: Optional[List[Node]] = None,
    ):
        super().__init__(parent)
        self.tag = tag
        self.children = children if children is not None else []

    @property
    def start(self) -> Optional[int]:
        first_token = self.find(
            lambda n: isinstance(n, TokenNode), iter_=PostOrderTreeIterator
        )
        return first_token.start if first_token else None

    @property
    def end(self) -> Optional[int]:
        last_token = self.find(
            lambda n: isinstance(n, TokenNode),
            iter_=PostOrderTreeIterator,
            reverse_children=True,
        )
        return last_token.end if last_token else None

    def iter_find_all(
        self,
        filter_: Union[CallableFilter, KeyValueFilter, None],
        max_count: int = 0,
        iter_: TreeIterator = LevelOrderTreeIterator,
        **kwargs,
    ) -> Iterable[Node]:
        """Iterate all nodes matching specified filter.

        Args:
          filter_: Describes what to search for. Might be:
            * Callable taking Node as an argument and returning True for accepted
              nodes.
            * Dict mapping Node attribute names to searched value or list of
              searched values.
          max_count: Stop searching after finding that many matching nodes.
          iter_: Tree iterator. Decides in what order nodes are visited.

        Yields:
          Nodes matching specified filter.
        """

        def as_list(v):
            return v if isinstance(v, list) else [v]

        if filter_ and not callable(filter_):
            filters = filter_

            def f(node):
                for attr, value in filters.items():
                    if not hasattr(node, attr):
                        return False
                    if getattr(node, attr) not in as_list(value):
                        return False
                return True

            filter_ = f

        for node in iter_(self, filter_, **kwargs):
            yield node
            max_count -= 1
            if max_count == 0:
                break

    def find(
        self,
        filter_: Union[CallableFilter, KeyValueFilter, None],
        iter_: TreeIterator = LevelOrderTreeIterator,
        **kwargs,
    ) -> Optional[Node]:
        """Find node matching specified filter.

        Args:
          filter_: Describes what to search for. Might be:
            * Callable taking Node as an argument and returning True for accepted
              node.
            * Dict mapping Node attribute names to searched value or list of
              searched values.
          iter_: Tree iterator. Decides in what order nodes are visited.

        Returns:
          First Node matching filter.
        """
        return next(
            self.iter_find_all(filter_, max_count=1, iter_=iter_, **kwargs), None
        )

    def find_all(
        self,
        filter_: Union[CallableFilter, KeyValueFilter, None],
        max_count: int = 0,
        iter_: TreeIterator = LevelOrderTreeIterator,
        **kwargs,
    ) -> List[Node]:
        """Find all nodes matching specified filter.

        Args:
          filter_: Describes what to search for. Might be:
            * Callable taking Node as an argument and returning True for accepted
              nodes.
            * Dict mapping Node attribute names to searched value or list of
              searched values.
          max_count: Stop searching after finding that many matching nodes.
          iter_: Tree iterator. Decides in what order nodes are visited.

        Returns:
          List of nodes matching specified filter.
        """
        return list(
            self.iter_find_all(filter_, max_count=max_count, iter_=iter_, **kwargs)
        )

    def to_formatted_string(self) -> str:
        tag = self.tag if self.tag == repr(self.tag)[1:-1] else repr(self.tag)
        return _colorize(["37", "1;97"], ["[", tag, "]"])


class RootNode(BranchNode):
    """Syntax tree root node."""

    def __init__(
        self,
        tag: str,
        syntax_data: Optional["SyntaxData"] = None,
        children: Optional[List[Node]] = None,
    ):
        super().__init__(tag, None, children)
        self._syntax_data = syntax_data

    @property
    def syntax_data(self) -> Optional["SyntaxData"]:
        return self._syntax_data


class LeafNode(Node):
    """Syntax tree leaf node.

    This specific class is used for null nodes.
    """

    @property
    def start(self) -> None:
        """Byte offset of token's first character in source text"""
        return None

    @property
    def end(self) -> None:
        """Byte offset of a character just past the token in source text."""
        return None

    def to_formatted_string(self) -> str:
        return _colorize(["90"], ["null"])


class TokenNode(LeafNode):
    """Tree node with token data

    Represents single token in a syntax tree.

    Attributes:
      tag (str): Token tag.
    """

    def __init__(self, tag: str, start: int, end: int, parent: Optional[Node] = None):
        super().__init__(parent)
        self.tag = tag
        self._start = start
        self._end = end

    @property
    def start(self) -> int:
        return self._start

    @property
    def end(self) -> int:
        return self._end

    def to_formatted_string(self) -> str:
        tag = self.tag if self.tag == repr(self.tag)[1:-1] else repr(self.tag)
        parts = [
            _colorize(["37", "1;97"], ["[", tag, "]"]),
            _colorize(["33", "93"], ["@(", self.start, "-", self.end, ")"]),
        ]
        text = self.text
        if self.tag != text:
            parts.append(_colorize(["32", "92"], ["'", repr(text)[1:-1], "'"]))
        return " ".join(parts)


class Token:
    """Token data

    Represents single token in tokens and rawtokens lists.

    Attributes:
      tag (str): Token tag.
      start (int): Byte offset of token's first character in source text.
      end (int): Byte offset of a character just past the token in source text.
      syntax_data (Optional["SyntaxData"]): Parent SyntaxData.
    """

    def __init__(
        self, tag: str, start: int, end: int, syntax_data: Optional["SyntaxData"] = None
    ):
        self.tag = tag
        self.start = start
        self.end = end
        self.syntax_data = syntax_data

    @property
    def text(self) -> str:
        """Token text in source code."""
        sd = self.syntax_data
        if sd and sd.source_code and self.end <= len(sd.source_code):
            return sd.source_code[self.start : self.end].decode("utf-8")
        return ""

    def __repr__(self) -> str:
        return _CSI_SEQUENCE.sub("", self.to_formatted_string())

    def to_formatted_string(self) -> str:
        tag = self.tag if self.tag == repr(self.tag)[1:-1] else repr(self.tag)
        parts = [
            _colorize(["37", "1;97"], ["[", tag, "]"]),
            _colorize(["33", "93"], ["@(", self.start, "-", self.end, ")"]),
            _colorize(["32", "92"], ["'", repr(self.text)[1:-1], "'"]),
        ]
        return " ".join(parts)


@dataclasses.dataclass
class Error:
    line: int
    column: int
    phase: str
    message: str = ""


@dataclasses.dataclass
class SyntaxData:
    source_code: Optional[str] = None
    tree: Optional[RootNode] = None
    tokens: Optional[List[Token]] = None
    rawtokens: Optional[List[Token]] = None
    errors: Optional[List[Error]] = None


class VeribleVerilogSyntax:
    """``verible-verilog-syntax`` wrapper.

    This class provides methods for running ``verible-verilog-syntax`` and
    transforming its output into Python data structures.

    Args:
      executable: path to ``verible-verilog-syntax`` binary.
    """

    def __init__(self, executable: str = "verible-verilog-syntax"):
        self.executable = executable

    @staticmethod
    def _transform_tree(tree, data: SyntaxData, skip_null: bool) -> RootNode:
        def transform(tree):
            if tree is None:
                return None
            if "children" in tree:
                children = [
                    transform(child) or LeafNode()
                    for child in tree["children"]
                    if not (skip_null and child is None)
                ]
                tag = tree["tag"]
                return BranchNode(tag, children=children)
            tag = tree["tag"]
            start = tree["start"]
            end = tree["end"]
            return TokenNode(tag, start, end)

        if "children" not in tree:
            return None

        children = [
            transform(child) or LeafNode()
            for child in tree["children"]
            if not (skip_null and child is None)
        ]
        tag = tree["tag"]
        return RootNode(tag, syntax_data=data, children=children)

    @staticmethod
    def _transform_tokens(tokens, data: SyntaxData) -> List[Token]:
        return [Token(t["tag"], t["start"], t["end"], data) for t in tokens]

    @staticmethod
    def _transform_errors(tokens) -> List[Error]:
        return [
            Error(t["line"], t["column"], t["phase"], t.get("message", None))
            for t in tokens
        ]

    def _parse(
        self, paths: List[str], input_: str = None, options: Dict[str, Any] = None
    ) -> Dict[str, SyntaxData]:
        """Common implementation of parse_* methods"""
        options = {
            "gen_tree": True,
            "skip_null": False,
            "gen_tokens": False,
            "gen_rawtokens": False,
            **(options or {}),
        }

        args = ["-export_json"]
        if options["gen_tree"]:
            args.append("-printtree")
        if options["gen_tokens"]:
            args.append("-printtokens")
        if options["gen_rawtokens"]:
            args.append("-printrawtokens")

        proc = subprocess.run(
            [self.executable, *args, *paths],
            stdout=subprocess.PIPE,
            input=input_,
            encoding="utf-8",
            check=False,
        )
        json_data = json.loads(proc.stdout)
        data = {}
        for file_path, file_json in json_data.items():
            file_data = SyntaxData()

            if file_path == "-":
                file_data.source_code = input_.encode("utf-8")
            else:
                with open(file_path, "rb") as f:
                    file_data.source_code = f.read()

            if "tree" in file_json:
                file_data.tree = VeribleVerilogSyntax._transform_tree(
                    file_json["tree"], file_data, options["skip_null"]
                )

            if "tokens" in file_json:
                file_data.tokens = VeribleVerilogSyntax._transform_tokens(
                    file_json["tokens"], file_data
                )

            if "rawtokens" in file_json:
                file_data.rawtokens = VeribleVerilogSyntax._transform_tokens(
                    file_json["rawtokens"], file_data
                )

            if "errors" in file_json:
                file_data.errors = VeribleVerilogSyntax._transform_errors(
                    file_json["errors"]
                )

            data[file_path] = file_data
        return data

    def parse_files(
        self, paths: List[str], options: Dict[str, Any] = None
    ) -> Dict[str, SyntaxData]:
        """Parse multiple SystemVerilog files.

        Args:
          paths: list of paths to files to parse.
          options: dict with parsing options.
            Available options:
              gen_tree (boolean): whether to generate syntax tree.
              skip_null (boolean): null nodes won't be stored in a tree if True.
              gen_tokens (boolean): whether to generate tokens list.
              gen_rawtokens (boolean): whether to generate raw token list.
            By default only ``gen_tree`` is True.

        Returns:
          A dict that maps file names to their parsing results in SyntaxData object.
        """
        return self._parse(paths, options=options)

    def parse_file(
        self, path: str, options: Dict[str, Any] = None
    ) -> Optional[SyntaxData]:
        """Parse single SystemVerilog file.

        Args:
          path: path to a file to parse.
          options: dict with parsing options.
            Available options:
              gen_tree (boolean): whether to generate syntax tree.
              skip_null (boolean): null nodes won't be stored in a tree if True.
              gen_tokens (boolean): whether to generate tokens list.
              gen_rawtokens (boolean): whether to generate raw token list.
            By default only ``gen_tree`` is True.

        Returns:
          Parsing results in SyntaxData object.
        """
        return self._parse([path], options=options).get(path, None)

    def parse_string(
        self, string: str, options: Dict[str, Any] = None
    ) -> Optional[SyntaxData]:
        """Parse a string with SystemVerilog code.

        Args:
          string: SystemVerilog code to parse.
          options: dict with parsing options.
            Available options:
              gen_tree (boolean): whether to generate syntax tree.
              skip_null (boolean): null nodes won't be stored in a tree if True.
              gen_tokens (boolean): whether to generate tokens list.
              gen_rawtokens (boolean): whether to generate raw token list.
            By default only ``gen_tree`` is True.

        Returns:
          Parsing results in SyntaxData object.
        """
        return self._parse(["-"], input_=string, options=options).get("-", None)

def check_protocol_manually(port, protocol_rec):

    for key, list_of_name_lists in protocol_rec.items():
        for list_of_names in list_of_name_lists:
            for name in list_of_names:
                if name in port:
                    return key, name

    return None, None

def convert_to_dictionary(data, recognize_dft_int=False, process_protocol_sig=False):
    """
    Converts parsed Verilog data into a structured dictionary, allowing for easier manipulation
    and retrieval of module information.

    Parameters:
    - data (ParseTree): The parse tree structure containing the entire Verilog design as parsed
                        by the Verible parser.
    - recognize_dft_int (bool): Flag to determine whether to recognize and process DFT interface signals.
    - process_protocol_sig (bool): Flag to determine whether to process specific protocol signals
                                   according to predefined patterns.

    The function processes various Verilog constructs such as modules and packages, extracting parameters,
    ports, and other significant elements, restructuring them into a dictionary. This dictionary includes
    details like port widths, directions, and specific protocol-related modifications if required.

    Returns:
    - dict: A dictionary containing structured Verilog module and package information.
            Modules are keyed by their names with values containing detailed information such as parameters,
            port lists, and other attributes.
    """
    protocols = {
        'axi': {'pattern':'axi_','prefix':'_AXI'},
        'axi-cdc': {'pattern':'xxx_','prefix':'_AXI'},
        'axis': {'pattern':'axis_','prefix':'_AXI'},
        'axis-cdc': {'pattern':'xxx_','prefix':'_AXI'},
        'apb_v3':  {'pattern':'apb_v3','prefix':'_APB_V3'},
        'apb_v3-cdc':  {'pattern':'xxx_','prefix':'_APB_V3'},
        'apb_v4':  {'pattern':'apb_v4','prefix':'_APB_V4'},
        'apb_v4-cdc':  {'pattern':'xxx_','prefix':'_APB_V4'},
        'ocpl': {'pattern':'ocpl_', 'prefix':'_OCPL'},
        'token': {'pattern':'tok_', 'unmatch':'ocpl_', 'prefix':'_TOK'},
        'token-cdc': {'pattern':'xxx_', 'prefix':'_TOK'},
    }
    if recognize_dft_int:
        protocols['vl_srv'] =  {'pattern':'vl_srv', 'prefix':''}
        #protocols['vl_sms'] = {'pattern':'vl_sms', 'prefix':''}

    role = {
        'master': ['_m','_m_1','_m_2','_I','_nm'],
        'slave': ['_s','_T','_ns'],
        'consumer' : ['_cons'],
        'producer' : ['_prod']
    }

    exclude_ports = ['_clk','_rst']
    non_exclude_ports = ['_rst_ack']

    modules = {}
    module_is_open = False
    packages = {}
    package_is_open = False
    out = ""
    for node in anytree.PreOrderIter(data.tree):
        if is_branch_node(node, "kModuleHeader"):
            first_port = True
            first_parameter = True
            if module_is_open:
                out += "\n);\n\n"

            module_is_open = True

            for c in node.children:
                if type(c) == TokenNode and c.tag == "SymbolIdentifier":
                    module_name = c.text
                    modules[module_name] = {}
                    modules[module_name]['parameters'] = {}
                    modules[module_name]['ports'] = {}
                    modules[module_name]['ports']['misc'] = {}
                    for protocol in protocols.keys():
                        modules[module_name]['ports'][protocol] = {}
                    modules[module_name]['imports'] = []
                    out += f"{module_name} "

                if type(c) == BranchNode and c.tag == "kPackageImportList":
                    list_of_tuples = [n.children for n in anytree.PreOrderIter(c)]
                    node_list = [item for t in list_of_tuples for item in t]
                    for c_ in node_list:
                        if type(c_) == TokenNode and c_.tag == "SymbolIdentifier":
                            pkg_name = c_.text
                            modules[module_name]['imports'].append(pkg_name)

        if is_branch_node(node, "kPackageDeclaration"):
            first_parameter = True
            if package_is_open:
                out += "\n);\n\n"

            package_is_open = True

            for c in node.children:
                if type(c) == TokenNode and c.tag == "SymbolIdentifier":
                    package_name = c.text
                    packages[package_name] = {}
                    packages[package_name]['parameters'] = {}
                    packages[package_name]['imports'] = []
                    out += f"{package_name} "

                if type(c) == BranchNode and c.tag == "kPackageImportList":
                    list_of_tuples = [n.children for n in anytree.PreOrderIter(c)]
                    node_list = [item for t in list_of_tuples for item in t]
                    for c_ in node_list:
                        if type(c_) == TokenNode and c_.tag == "SymbolIdentifier":
                            pkg_name = c_.text
                            packages[package_name]['imports'].append(pkg_name)

        if is_branch_node(node, "kParamDeclaration"):
            parameter = {}
            for c in node.children:
                #if c.text=='localparam':
                    # do not store localparams
                    #break
                if is_branch_node(c, "kParamType"):
                    for c_ in c.children:
                        # For params with no dim
                        if is_branch_node(c_, "kUnqualifiedId"):
                            param_name = c_.children[0].text
                            if package_is_open:
                                packages[package_name]['parameters'][param_name] = []
                            elif module_is_open:
                                modules[module_name]['parameters'][param_name] = []
                        # For params with an unpacked dim (unpacked dim not added to dict for now)
                        if type(c_) == TokenNode and c_.tag == "SymbolIdentifier":
                            param_name = c_.text
                            if package_is_open:
                                packages[package_name]['parameters'][param_name] = []
                            elif module_is_open:
                                modules[module_name]['parameters'][param_name] = []

                if is_branch_node(c, "kTrailingAssign"):
                    for c_ in [n.children for n in anytree.PreOrderIter(c)]:
                        for c__ in c_:
                            if type(c__) == TokenNode and (c__.tag == "TK_DecNumber" or c__.tag == "TK_DecBase" or c__.tag == "TK_DecDigits"):
                                if package_is_open:
                                    packages[package_name]['parameters'][param_name].append(c__.text)
                                elif module_is_open:
                                    modules[module_name]['parameters'][param_name].append(c__.text)




        if is_branch_node(node, "kPortDeclaration"):
            width = []
            symbol_id = ""
            unpacked_dim = []
            direction = None
            packed_dim = 1
            sig_type = "logic"
            sig_dir = ""
            for c in node.children:
                # get direction
                if type(c) == TokenNode and c.tag == "input":
                    sig_dir = "input"
                if type(c) == TokenNode and c.tag == "output":
                    sig_dir = "output"
                if type(c) == TokenNode and c.tag == "inout":
                    sig_dir = "inout"
                    sig_type = "wire"

                # get sig type
                if type(c) == TokenNode and c.tag == "wire":
                  sig_type = "wire"

                direction = f'{sig_dir} {sig_type}'

                # get associated widths
                if is_branch_node(c, "kDataType"):
                    for c_ in [n.children for n in anytree.PreOrderIter(c)]:
                        for c__ in c_:
                            if type(c__) == BranchNode and c__.tag == "kPackedDimensions":
                                packed_dim = c__.text
                            if type(c__) == TokenNode and c__.tag == "MacroIdentifier":
                                #import pdb; pdb.set_trace()
                                width.append(c__.text)
                            if type(c__) == TokenNode and c__.tag == "SymbolIdentifier":
                                #import pdb; pdb.set_trace()
                                if symbol_id:
                                    symbol_id += "::"
                                symbol_id += c__.text
                                width.append(c__.text)
                            if type(c__) == TokenNode and c__.tag == "TK_DecNumber":
                                width.append(c__.text)

                if is_branch_node(c, "kUnpackedDimensions"):
                    for c_ in [n.children for n in anytree.PreOrderIter(c)]:
                        for c__ in c_:
                            if type(c__) == TokenNode and c__.tag == "SymbolIdentifier":
                                #import pdb; pdb.set_trace()
                                unpacked_dim.append(c__.text)
                            if type(c__) == TokenNode and c__.tag == "TK_DecNumber":
                                unpacked_dim.append(c__.text)

                if is_branch_node(c, "kUnqualifiedId"):
                    port = c.children[0].text

                    def assign_axi_params(port, prtcl, prtcl_port):
                        if prtcl == 'axi' and 'rid' in port:
                            try:
                                modules[module_name]['ports'][prtcl][prtcl_port]['id_width'] = int(width[0])+1
                            except:
                                modules[module_name]['ports'][prtcl][prtcl_port]['id_width'] = width[0]
                        if prtcl == 'axi' and 'raddr' in port:
                            try:
                                modules[module_name]['ports'][prtcl][prtcl_port]['addr_width'] = int(width[0])+1
                            except:
                                modules[module_name]['ports'][prtcl][prtcl_port]['addr_width'] = width[0]
                        if prtcl == 'axi' and ('wdata' in port or 'rdata' in port):
                            try:
                                modules[module_name]['ports'][prtcl][prtcl_port]['data_width'] = int(width[0])+1
                                modules[module_name]['ports'][prtcl][prtcl_port]['wstrb_width'] = int((int(width[0])+1)/8)
                            except:
                                modules[module_name]['ports'][prtcl][prtcl_port]['data_width'] = width[0]
                        if prtcl == 'axi' and ('wlen' in port or 'rlen' in port):
                            try:
                                modules[module_name]['ports'][prtcl][prtcl_port]['len_width'] = int(width[0])+1
                            except:
                                modules[module_name]['ports'][prtcl][prtcl_port]['len_width'] = width[0]
                        if prtcl == 'axi' and 'wstrb' in port:
                            try:
                                modules[module_name]['ports'][prtcl][prtcl_port]['wstrb_width'] = int(width[0])+1
                            except:
                                modules[module_name]['ports'][prtcl][prtcl_port]['wstrb_width'] = width[0]
                        if (prtcl == 'axi'
                            and ((('awvalid' in port))
                                 or ('arvalid' in port)
                                 or ('arready' in port)
                                 or ('awready' in port))) or (prtcl == 'axis' and 'valid' in port):
                            if 'output' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'output'
                            elif 'input' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'input'
                        if (prtcl == 'apb_v3' or prtcl == 'apb_v4') and 'paddr' in port:
                            if 'output' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'output'
                            elif 'input' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'input'
                        if prtcl == "ocpl":
                            modules[module_name]['ports'][prtcl][prtcl_port].setdefault('ocpl_ports', {})
                            modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port] = {'name' : port}
                            if symbol_id:
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['nr_tokens'] = ""
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['direction'] = f"{direction}".replace('logic', symbol_id)
                            elif packed_dim:
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['nr_tokens'] = packed_dim if packed_dim !=1 else ""
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['direction'] = direction
                            elif len(width) > 1:
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['nr_tokens'] = [f"{width[0]}::{width[1]}-1"]
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['direction'] = direction
                            else:
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['nr_tokens'] = ""
                                modules[module_name]['ports'][prtcl][prtcl_port]['ocpl_ports'][port]['direction'] = direction
                        if prtcl == "token" and "vld" in port:
                            if len(width) > 3:
                                modules[module_name]['ports'][prtcl][prtcl_port]['nr_tokens'] = [width[1]]
                            else:
                                modules[module_name]['ports'][prtcl][prtcl_port]['nr_tokens'] = [width[0]]
                            if 'output' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'output'
                            elif 'input' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'input'
                        if prtcl == "vl_srv" and port.endswith("WRCK"):
                            if 'output' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'output'
                            elif 'input' in direction:
                                modules[module_name]['ports'][prtcl][prtcl_port]['direction'] = 'input'
                        if prtcl == "vl_srv" and port.endswith("sfp_fail"):
                            modules[module_name]['ports'][prtcl][prtcl_port]['has_fail'] = True

                    def get_replacement(port):

                        if '_I1_' in port:
                            replace = True
                            replacement = port.replace("_I1_","_I_")
                        else:
                            replace = False
                            replacement = ''

                        return replace, replacement

                    def detect_role(port):
                      for roleName in role.keys():
                        if any(prtcl_port.endswith(sym) for sym in role[roleName]):
                          return roleName

                      return ""

                    def add_port_to_dict(port, prtcl, prtcl_port, prefix):
                        search_obj = re.search(r"_\d+$",prtcl_port)
                        if search_obj != None:
                          flattend = True
                          flattend_value = int(search_obj.group()[1:])
                          # Remove flattend bus idx from prtcl_port
                          prtcl_port = re.sub(r"_\d+","",prtcl_port)
                        else:
                          flattend = False
                          flattend_value = 0

                        if prtcl_port not in modules[module_name]['ports'][prtcl].keys():
                            modules[module_name]['ports'][prtcl][prtcl_port] = {
                                'type': detect_role(prtcl_port),
                                'ports':[],
                                "param_pref": f'{module_name}_{prtcl_port}'.upper(),
                                "direction" : "",
                                "flattend" : flattend}

                        assign_axi_params(port,prtcl,prtcl_port)
                        replace, replacement = get_replacement(port)
                        modules[module_name]['ports'][prtcl][prtcl_port]['ports'].append({
                            "port":port,
                            "width":width,
                            "dir":direction,
                            "replace":replace,
                            "replacement":replacement,
                            "unpacked_dim" : unpacked_dim,
                            "packed_dim" : packed_dim,
                            "flattend_value" : flattend_value,
                            "symbol_id" : symbol_id})

                        if len(width)>=3:
                            param_pref = '_'.join(width[0].split('_')[:-2:])

                            modules[module_name]['ports'][prtcl][prtcl_port]['param_pref']=param_pref

                    # if protocol is not recognized through naming convention, check whether it can be recognized manually:
                    recognized_protocol = any(prtcl['pattern'] in port for prtcl in protocols.values())
                    protocol_excluded_port = any(exclude in port for exclude in exclude_ports) and not any(exclude in port for exclude in non_exclude_ports)

                    if process_protocol_sig and recognized_protocol and not protocol_excluded_port:
                        for prtcl, prot_descr in protocols.items():
                            if prot_descr['pattern'] in port and ('unmatch' not in prot_descr or prot_descr['unmatch'] not in port):
                                # If the port name starts with the protocol name. There is no name available for the entire interface other than the protocol name itself.
                                if port.startswith(prot_descr['pattern']) and prot_descr["pattern"] in ['vl_sms', 'vl_srv']:
                                    prtcl_port = prot_descr['pattern'].rstrip('_')
                                else:
                                    if prot_descr['pattern'] == 'vl_srv':
                                        prtcl_port = port.split(prot_descr['pattern'])[0] + prot_descr['pattern']
                                    else:
                                        # If the post_fix of the port is only 1 char, expand the postfix to the second to last '_' in the port name.
                                        if len(port.split('_')[-1]) > 1:
                                            prtcl_port = '_'.join(port.split('_')[:-1])
                                        else:
                                            prtcl_port = '_'.join(port.split('_')[:-2])
                                if 'cdc' in port:
                                    prtcl_port = port.split('_cdc')[0]
                                    prtcl = prtcl + '-cdc' if 'cdc' in port else prtcl
                                add_port_to_dict(port, prtcl, prtcl_port,prot_descr['prefix'])
                    else:
                        modules[module_name]['ports']['misc'][port] = {"width":width, "dir": direction, "unpacked_dim" : unpacked_dim, "packed_dim" : packed_dim, "symbol_id" : symbol_id}

                    out += emit_port_item(first_port, port)

                    if first_port:
                        first_port = False

    #print (modules)
    return modules if module_is_open else packages


def main():
    parser = argparse.ArgumentParser(
        description="(System)Verilog helper tool based on verible."
    )
    parser.add_argument(
        "verilog_file", metavar="input", type=str, help="Config file for test runner."
    )
    parser.add_argument(
        "-p",
        "--print-tree",
        action="store_true",
        help="Print the source tree of the verilog file.",
    )
    parser.add_argument(
        "-i",
        "--instantiation",
        action="store_true",
        help="Prints a list of instantiations from all modules in the file.",
    )
    parser.add_argument(
        "-c",
        "--convert-to-hjson",
        action="store_true",
        help="creates hjson file describing the module, imports and io",
    )
    parser.add_argument(
        "-a",
        "--append-port-name",
        action="store_true",
        help="append signal name with @_ in ( )",
    )
    parser.add_argument(
        "-port_dir",
        "--port-dir",
        action="store_true",
        help="print interface signal list with direction for formality usage"
    )


    args = parser.parse_args()
    vs = VeribleVerilogSyntax()
    data = vs.parse_file(args.verilog_file)

    if not data.tree:
        logging.error("Error parsing tree.")
        return 1

    if args.print_tree:
        for prefix, _, node in anytree.RenderTree(data.tree):
            print(f"\033[90m{prefix}\033[0m{node.to_formatted_string()}")

    # Print instantation tree.
    # TODO(zarubaf): Re-factor into own library and clean up parsing from
    # emission.
    if args.instantiation or args.append_port_name:
        module_is_open = False
        out = ""
        for node in anytree.PreOrderIter(data.tree):
            if is_branch_node(node, "kModuleHeader"):
                first_port = True
                first_parameter = True
                if module_is_open:
                    out += "\n);\n\n"

                module_is_open = True

                for c in node.children:
                    if type(c) == TokenNode and c.tag == "SymbolIdentifier":
                        module_name = c.text
                        out += f"{module_name} "

            if is_branch_node(node, "kParamDeclaration"):
                for c in node.children:
                    if is_branch_node(c, "kParamType"):
                        for c in c.children:
                            parameter = None
                            # Two ways of getting parameters
                            if is_branch_node(c, "kUnqualifiedId"):
                                parameter = c.children[0].text
                            if type(c) == TokenNode and c.tag == "SymbolIdentifier":
                                parameter = c.text

                            if parameter:
                                if first_parameter:
                                    out += "#(\n"
                                out += emit_port_item(first_parameter, parameter)
                                if first_parameter:
                                    first_parameter = False

            if is_branch_node(node, "kPortDeclaration"):
                for c in node.children:
                    if is_branch_node(c, "kUnqualifiedId"):
                        port = c.children[0].text

                        if first_port:
                            if not first_parameter:
                                out += "\n) "
                            out += f"i_{module_name} (\n"

                        if args.append_port_name:
                          out += emit_port_item_a(first_port, port)
                        else:
                          out += emit_port_item(first_port, port)

                        if first_port:
                            first_port = False

        out += "\n);"
        print(out)
        return 0


    if args.convert_to_hjson:
        ver_dict = convert_to_dictionary(data)
        with open("{}.hjson".format(args.verilog_file), "w") as outfile:
            hjson.dump(ver_dict, outfile)
        return 0

    if args.port_dir:
        module_is_open = False
        out = ""
        for node in anytree.PreOrderIter(data.tree):
            if is_branch_node(node, "kPortDeclaration"):
                dir = ""
                port = ""
                for c in node.children:
                    if type(c) == TokenNode and c.tag in ["input", "output", "inout"]:
                        dir = c.tag.replace("put","")
                    if is_branch_node(c, "kUnqualifiedId"):
                        port = c.children[0].text
                        out += f"set_direction {port} {dir}\n"
        print(out)
        return 0


def is_branch_node(node, node_tag):
    return type(node) == BranchNode and node.tag == node_tag

def get_branch_node(node):
    if type(node) == BranchNode:
      return node.tag

def emit_port_item(first, port):
    comma = ",\n" if not first else ""
    return f"{comma}  .{port} ( )"

def emit_port_item_a(first, port):
    comma = ",\n" if not first else ""
    return f"{comma}  .{port} ( @_{port} )"


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
