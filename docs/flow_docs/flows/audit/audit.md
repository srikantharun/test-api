# RTL Audit Flow 

## Objectives:

- Enforce a consistent approach to RTL audit and code quality
- Allow for focused signoffs with minimal effort
- Ease of peer reviews
- Reuse of signoffs from common libraries
- Identify and document designer intent

## Approach

### Ideal world

Auditing is a process that should be applied at as many points as possible throughout our flow.
Every tool run should have logs (and where appropriate reports) analyzed for correctness. And warning or error should be signed off, and that sign off should be as precise as possible. For example, use of wild cards could sign off many warnings, with some unintentional ones along the way.

Signing off every warning many seem extreme and be very expensive in terms of engineering resource. However, the audit tool aims to minimise effort requirements by decoupling the warnings from the designer intent. For example, take the following piece of code (excuse the example I'm not putting through the tools and am imagining the warnings generated):

```SystemVerilog
logic signed [3:0] a, b;
logic [3:0] c;
always_comb a = b + c;
```

Almost every tool will warn that there is some form of arithmetic overflow present, b+c returns a width of 5 bits which is being coerced to 4 by assign to a. 

```SystemVerilog
logic signed [3:0] a, b;
logic [3:0] c;
always_comb a = b + c; // ASO-ARITHOVFL,ASO-U2SCONV : top bit of result is not required
```
 
As the designer intent is in the RTL code, a signoff can be generated with filename and line number. The same signoff generates the relevant signoffs for all tools within the Axelera flow meaning 1 comment can signoff all warnings from that line. 

Signoff comments starting at the beginning of the line will apply for the line below

```SystemVerilog
logic signed [3:0] a, b;
logic [3:0] c;
//ASO-ARITHOVFL : top bit of result is not required.
always_comb a = b + c; // ASO-U2SCONV : c is range 0 to 3
```

As code changes (lines added / removed) the signoff stays with the code it's signing off, reducing maintenance of signoff files.

### What if we can't modify RTL?

Not all code is our own. 3rd party IP is an example of that. We shouldn't modify their code.
In addition, there may be the requirement to sign off something outside of the RTL code base e.g. a tool version number, or perhaps a more global signoff is required, all messages of a particular type.

In these cases a standalone signoff file can be used, based upon codes:

```
ASO-ARITHOVFL : top bit of result is not required. (rtl/example.sv,7)
ASO-U2SCONV : c is range 0 to 3 (rtl/example.sv,7)
```

Or via a regular expression:

```
ASO-REGEXP "Warning: No filename specified .*" : RAM contents are expected to be empty.
```

## Summary of formats

In line RTL:

```
ASO-<code> : <signoff comment>
```

Standalone Signoff file (code based)

```
ASO-<code> : <signoff comment> (<filename>,<linenumber>)
```

Standalone Signoff freeform regexp)

```
ASO-REGEXP <regexp> : <signoff comment>
```

# Required Work

The audit tool comprises of the following actions:

1) Log Parsing

Logs are analyzed and the following is extracted:
- A list of all warnings
- A list of all errors
- A dictionary of metrics


2) RTL based signoff

Read RTL database and compile list of signoffs

3) Non RTL base signoff 

Read standalone signoff files and compile list of signoffs

4) Match signoffs to warnings

5) Generate Reports:

- signoff <-> warning matches
- unsigned off warnings / errors
- unused signoffs

6) Audit Review:

- Identify reviewed signoffs
- Next review, only review signoff deltas

7) Build up Signoff Code and Warning database


# Demo from Flow Work Group

~~https://axeleraai-my.sharepoint.com/:v:/g/personal/yi_lu_axelera_ai/EW8UsQTeFG1LgM0oFZGgwjIBgIEcrZb7P_Q4IsDIdeFxfA?referrer=Teams.TEAMS-ELECTRON&referrerScenario=MeetingChicletGetLink.view.view~~

https://axeleraai.sharepoint.com/:v:/r/sites/AXELERAAI-ResearchandDevelopment/Gedeelde%20documenten/Research%20and%20Development/hw/projects/europa/Flow/FLOW%20Working-Group-20231212_111018-Meeting%20Recording.mp4?csf=1&web=1&e=RDAeDb
