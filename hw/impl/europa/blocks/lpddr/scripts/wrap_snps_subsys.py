
class SimplePort:
    def __init__(self, name, width, direction):
        self.name = name
        self.width = width
        self.direction = direction
        self.tie = False
        self.unconnected = False
        self.type = "logic"
        self.force = False
        self.local = False
        self.dont_expose = False
        self.not_on_p_wrapper = False

    def check_if_matches_pattern(self, str_patterns):
        def pattern_check(self,str_pattern):
            return (str_pattern.startswith("*") and self.name.endswith(str_pattern[1:])) or (str_pattern.endswith("*") and self.name.startswith(str_pattern[:-1])) or self.name == str_pattern
        
        if isinstance(str_patterns, list):
            return any([pattern_check(self,str_pattern) for str_pattern in str_patterns])
        else:
            return pattern_check(self,str_patterns)
    
    def __str__(self):
        return f"Name: {self.name}, Direction: {self.direction}, Width: {self.width}"

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return self.name == other.name and self.width == other.width and self.direction == other.direction

    def __hash__(self):
        return hash((self.name, self.width, self.direction))


import re
import hjson
import mako.template
import os

REPO_ROOT = os.environ["REPO_ROOT"]
DDR_SUBSYSTEM_RTL_PATH = os.environ['DDR_SUBSYSTEM_RTL_PATH']
def calculate_width(width_str):
    if width_str:
        match = re.match(r'\[(\d+):(\d+)\]', width_str)
        if match:
            x, y = int(match.group(1)), int(match.group(2))
            return abs(x - y) + 1
    return 1

def generate_template(template_name, port_map, output_name, wrapper_port_map=None):
    # Pass the port_map to the mako template and render it
    template = mako.template.Template(filename=f"{REPO_ROOT}/hw/impl/europa/blocks/lpddr/scripts/{template_name}")
    rendered_code = template.render(port_map=port_map, wrapper_port_map=wrapper_port_map)

    # Write the rendered code to an output file
    output_file_path = f"{REPO_ROOT}/hw/impl/europa/blocks/lpddr/rtl/generated/{output_name}"
    with open(output_file_path, "w") as output_file:
        output_file.write(rendered_code)


# Read the Verilog code from a file
with open(f"{DDR_SUBSYSTEM_RTL_PATH}/src/snps_ddr_subsystem.v", "r") as f:
    verilog_code = f.read()

# Read the HJSON file
with open(f"{REPO_ROOT}/hw/impl/europa/blocks/lpddr/scripts/wrap_snps_subsys.hjson", "r") as f:
    hjson_code = f.read()
wrap_config = hjson.loads(hjson_code)

# Regular expression to match input statements
input_pattern = re.compile(r'input\s+(\[\d+:\d+\]\s+)?(\w+);')
output_pattern = re.compile(r'output\s+(\[\d+:\d+\]\s+)?(\w+);')
inout_pattern = re.compile(r'inout\s+(\[\d+:\d+\]\s+)?(\w+);')

input_ports = []
for input_match in input_pattern.findall(verilog_code):
    width = calculate_width(input_match[0])
    name = input_match[1]
    input_ports.append(SimplePort(name, width, "input"))

output_ports = []
for output_match in output_pattern.findall(verilog_code):
    width = calculate_width(output_match[0])
    name = output_match[1]
    output_ports.append(SimplePort(name, width, "output"))

inout_ports = []
for inout_match in inout_pattern.findall(verilog_code):
    width = calculate_width(inout_match[0])
    name = inout_match[1]
    inout_ports.append(SimplePort(name, width, "inout"))

all_ports = input_ports + output_ports + inout_ports
# Make a dictionary of all ports with the orignal port as the key and the renamed port as the value
port_map = {}
for port in all_ports:
    # Don't alter the original name in case we don't want to, don't expose the port upward, or make a local connection to it.
    if port.check_if_matches_pattern(wrap_config["dont_prefix"]) or port.check_if_matches_pattern(wrap_config["dont_expose"]) or port.name in wrap_config["connect_to"]:
        new_port_name = port.name
    else:
        new_port_name = f"i_{port.name}" if port.direction == "input" else f"o_{port.name}"
        new_port_name = new_port_name.lower()
        for postfix in wrap_config["snps_postfix_removal"]:
            if new_port_name.endswith(postfix):
                new_port_name = new_port_name[:-len(postfix)]
                break

    new_port = SimplePort(new_port_name, port.width, port.direction)
    port_map[port] = new_port

# Setup port dict for wrapper gen
for snps_port, ax_port in port_map.items():

    # Look for AXI ports and rename them
    for snps_axi_port_postfix in wrap_config["axi_port_naming"]:
        if snps_port.name[:-2] == snps_axi_port_postfix:
            ax_port.name = f"{'i_' if snps_port.direction=='input' else 'o_'}{wrap_config['axi']}_{snps_port.name[:-2]}"
            break

    # Look for APB ports and rename them
    for snps_apb_port_prefix in wrap_config["apb_port_naming"]:
        if snps_port.name == snps_apb_port_prefix:
            ax_port.name = f"{'i_' if snps_port.direction=='input' else 'o_'}{wrap_config['apb']}_{snps_port.name}"
            break

    # Look for input ports that are tied to 0 or 1
    if snps_port.direction == "input":
        for tie_pattern, tie_value in wrap_config["tie_to"].items():
            if snps_port.check_if_matches_pattern(tie_pattern):
                    ax_port.tie = True
                    ax_port.name = tie_value
                    break
        
    # Check which output ports remain unconnected
    if snps_port.direction == "output":
        for unconnected_pattern in wrap_config["unconnected_list"]:
            if snps_port.check_if_matches_pattern(unconnected_pattern):
                ax_port.unconnected = True
                break

    # Check if the port is a clock port that will be merged with other clock ports
    for new_port_name, snps_port_name in wrap_config["rename_ports"].items():
        if isinstance(snps_port_name, list):
            if snps_port.name in snps_port_name:
                if snps_port.direction == "output":
                    raise ValueError(f"Output port {snps_port.name} cannot be broadcasted to multiple snps ports, this create a multiple driver issue in RTL")
                ax_port.name = new_port_name
        else:
            if snps_port.name == snps_port_name:
                ax_port.name = new_port_name

    # Check if we make a local connection to this port
    for snps_port_name, conn_port_name in wrap_config["connect_to"].items():
        if snps_port.name == snps_port_name:
            snps_port.force = True
            for snps_conn_port in port_map.keys():
                if snps_conn_port.name == conn_port_name:
                    port_map[snps_port] = port_map[snps_conn_port]
                    port_map[snps_port].local = True
                    port_map[snps_port].dont_expose = True
                    port_map[snps_port].force = True
                    print(f"DEBUG: snps port: {snps_port}, ax_port {port_map[snps_port]}")

    # Check for ports that we do not want to expose upwards
    for snps_port_name in wrap_config["dont_expose"]:
        if snps_port.name == snps_port_name:
            ax_port.dont_expose = True 
            snps_port.not_on_p_wrapper = True
            snps_port.force = True

    # Check if the port should use wire type instead of the default logic type
    for port_pattern in wrap_config["use_wires"]:
        if snps_port.check_if_matches_pattern(port_pattern):
            ax_port.type = "wire"


generate_template("wrap_snps_subsys.mako", port_map, "lpddr_subsys_wrapper.sv")

# Adapt port list for inverse wrapper gen
for snps_port, ax_port in port_map.items():
    # Check if the port is one we connect to a csr or some other start/endpoint in the lpddr_p wrapper. In that case it still needs a force in the inverse wrapper
    for port_pattern in wrap_config['ends_in_p_wrapper']:
        if snps_port.check_if_matches_pattern(port_pattern) or ax_port.check_if_matches_pattern(port_pattern):
            snps_port.force = True
            ax_port.not_on_p_wrapper = True
            # print(f"DEBUG: {snps_port} will end in p wrapper logic, adding force.")

wrapper_ports = {}
for wrapper_port_name, wrapper_port_conn in wrap_config["added_in_p_wrapper"].items():
    for ax_port in port_map.values():
        if wrapper_port_name == ax_port.name:
            print("DEBUG: {wrapper_port} already included in ax_ports")
        else:
            wrapper_port_direction = "input" if wrapper_port_name.startswith("i_") else "output";
            wrapper_port = SimplePort(wrapper_port_name, 0, wrapper_port_direction)
            wrapper_ports[wrapper_port] = wrapper_port_conn

for ax_port in port_map.values():
    if ax_port.name in wrap_config["renamed_in_p_wrapper"]:
        ax_port.name = wrap_config["renamed_in_p_wrapper"][ax_port.name]

generate_template("inv_wrap_snps_subsys.mako", port_map, "lpddr_subsys_inv_wrapper.sv", wrapper_port_map=wrapper_ports)


