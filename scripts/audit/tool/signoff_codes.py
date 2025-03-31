
codes = {

    'PARAM' :           { 'rtla'     : [r"Warning:\s+%(file)s:%(line)d: Parameter keyword used in local parameter declaration. \(VER-329\)"]},
    'UNUSED_INPUT' :    { 'spyglass' : [r"\[\S+\]\s+W240\s+Warning\s+%(file)s\s+%(line)d\s+\d+\s+Input '.*' declared but not read.\[Hierarchy: ':.*'\]"]},
    'UNUSED_OUTPUT' :   { 'spyglass' : [r"\[\S+\]\s+W287b\s+Warning\s+%(file)s\s+%(line)d\s+\d+\s+Instance output port '.*' is not connected"],
                          'questa'   : [r"\*\*\s+Warning: %(file)s\(%(inst_name_line)d\): \(vopt-2871\) \[TFMPC\] - Missing connection for port '%(port)s'\. .*"]},
    'UNUSED_VARIABLE' : { 'spyglass' : [r"\[\S+\]\s+W528\s+Warning\s+%(file)s\s+%(line)d\s+\d+\s+Variable '.* set but not read.\[Hierarchy: ':.*'\]"]},
    'MULTI_ASSIGN' :    { 'spyglass' : [r"\[\S+\]\s+W415a\s+Warning\s+%(file)s\s+%(line)d\s+\d+\s+Signal.*is being assigned multiple times \( previous assignment at line \d+ \) in same always block \[Hierarchy: ':.*'\]"]},
    'UNDRIVEN_INPUT' :  { 'spyglass' : [r"\[\S+\]\s+UndrivenInTerm-ML\s+Error\s+%(file)s\s+%(line)d\s+\d+\s+Detected undriven input terminal .*"]},
    'BLOCKING_ASSIGN' : { 'spyglass' : [r"\[\S+\]\s+W336\s+Error\s+%(file)s\s+%(line)d\s+\d+\s+Blocking assignment '.*' used inside a 'FlipFlop' inferred sequential block"]},
    'BLOCKING_ASSIGN' : { 'code_grep': [r"%(file)s:\s*// verilog_lint: waive-(?:start|stop) always-ff-non-blocking.*"]},
}
