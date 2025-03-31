# New Joiners Guide
## First steps
- Contact [Fabrizio Denisi](mailto:f.denisi@wesystem.it) (f.denisi@wesystem.it) to finish your laptop setup, if you haven't already.
	- **Note: In teams, the only Fabrizio you will find is Fabrizio del Maffeo, our CEO, who is not the laptop setup guy ;)**.
	- As part of setup, Fabrizio will set up a personal user for you instead of ITadmin. A good idea will be for you to open a new user yourself (you'll be choosing the username anyways), and download all the apps you'll need there, to not spam ITadmin user with your credentials.
	- another note - Fabrizio will install Edge as the default browser, so you might already download it yourself.
- Permissions you'll need:
	- [Triton (last project) git repo](https://git.axelera.ai/ai-hw-team/triton) - ask your manager (Andrew/Antoine).
	- [Europa (current project) git repo](https://git.axelera.ai/prod/europa) - ask your manager (Andrew/Antoine).
	- [Europa planning git repo](https://git.axelera.ai/ai-dv-team/dv-europa-planning) - ask your manager (Andrew/Antoine).
	- [Europa architecture documentation](https://axeleraai.atlassian.net/wiki/spaces/archrd/pages/257556493/Europa) - check if you have access, if not, ask your manager (Andrew/Antoine).
	- [ICDF (python ref model) git repo](https://git.axelera.ai/dev/rd/IntraCoreDataFlow) - ask Pascal Hager, Arch team lead. **note** - there's a special branch for verification ref model.
	- [R&D sharepoint](https://axeleraai.sharepoint.com/:f:/r/sites/AXELERAAI-ResearchandDevelopment/Gedeelde%20documenten/Research%20and%20Development?csf=1&web=1&e=Ho39U3) - you won't have automatic access to all of it. you'll only see howto dir. open it and there will be instructions on how to set up the access correctly (Onboarding\_IT_setup/SharePoint setup). Ask your manager for permissions for hw folder. After getting permissions you should also see hw folder.
	- htz1 remote compute farm & Gitlab account. Ask [Amedeo Scuotto](mailto:amedeo.scuotto@axelera.ai) to set up accounts for you. If needed, ask for Veloce access (Veloce is our emulation platform. If you're not sure - ask your manager).
		- **note:** you'll find more info on how to setup ssh keys for your remote connection, how to setup veloce, and how to setup your code editors later on in this document 
	- After you have a gitlab account, configure two-factor authentification on gitlab

## People
You can see our org chart in teams, and a more informative excel on Europa project [here](https://axeleraai-my.sharepoint.com/:x:/g/personal/jonathan_ferguson_axelera_ai/EW4vctIZVrZGjvLqKaYzYskBB8NiyfiwEXEeB8mNXmrc-A?e=Dca1vy&wdOrigin=TEAMS-MAGLEV.p2p_ns.rwc&wdExp=TEAMS-TREATMENT&wdhostclicktime=1714475284743&web=1),
but general names you should know:

- Andrew Bond (Andy) - Verification team lead.
- Mrudula Gore (Mru) - Design team lead.
- Pascal Hager - Arch team lead.
- Job Jacobs - HR team.
- Vera Kapell - HR team, the person to ask payroll related questions.
- Karin den Heijer - HR team, the person to ask about office supplies/computer supplies questions.

Everyone is generally very happy to help and explain, so feel free to ask anything you're not sure about.

## Weekly meetings

Three meetings are scheduled every week:

- A short stand-up meeting on tuesday with the rest of the team. The goal is to give a very quick overview of your progress, using the "3Ps": Priority, Progress and Problems.

- A 1-to-1(1-2-1) meeting with your manager, to discuss more in details about your work, your aspirations, etc...

- A Verification Weekly with the team on friday, to sum up what everybody has done this week, what's to come, and what are the news related to the project. There's a git repo with a weekly branch, in which every team member has his own folder where he updates what he did (just update in the same branch & commit).

## READMEs
Most directories in our git repos (especially top dirs) have README files. Please read them - they provide valuable info on how to run/compile stuff, and about the project structure.

##  Useful links
- For leave/vacation notice and personal detail updations: [BambooHR](https://axeleraai.bamboohr.com)
- For sick leave : Mail to your Manager, HR (Vera/Job) in the morning.
- 1-2-1 and goals : [Lattice](https://axelera.latticehq.com)
- Salary (payslip) site: [ADP](https://online.emea.adp.com/signin/v1?APPID=MCPGlobalPortal&productId=96b3a3d1-e9e7-6676-e053-3505430b558d&returnURL=https://portal.people.adp.com/gvservice/wtsso/logon&callingAppId=MCPGlobalPortal&TARGET=-SM-https://portal.people.adp.com/gvservice/wtsso/logon)
- Expense claims : [Expensify](https://www.expensify.com)
- For travel and booking : [Travelperk](https://app.travelperk.com)
- Synopsys documentation - [Synopsys](https://solvnet.synopsys.com). Site ID for registration is: 48285
- Referral and interview site: [Ashby](https://app.ashbyhq.com)

## Workspace setup (htz1)

- Retrieve your ssh key: `cat ~/.ssh/id_rsa.pub`. If the file does not exist, you can generate it with the ssh-keygen` command. Add your key to your gitlab account in Preferences->SSH keys->add new key. In the 'Expiration Date' box, delete the date so that it never expires.

- Create a new folder with your name in the workspace area: `mkdir -p /home/projects_2/workspace/$USER`. This directory is your work area where you will clone and work on different projects. Setting up an alias/symlink to cd right into it is very handy.

## Veloce setup

Detailed instructions for the veloce setup and usage can be found [here](https://ai-hw-team.doc.axelera.ai/triton/user_guides/emulation).

In short:
- Connect to the emulator by using the `veloce` command (alias set up by the IT in your bashrc). It is equivalent to:
```bash
alias veloce='ssh -X -Y 10.4.1.10'
```

- As per the documentation, the following setup needs to be done on your first connection:
```bash
/home/tools/scripts/setup_hosts.sh
```

- Create a `$USER` directory in `/home/data2` and add the generated SSH key to gitlab enterprise (similarly to the workspace setup above). This will be your workspace folder on the veloce, like `/home/projects_2/workspace/$USER` on htz1.

## Editor setup

### Neovim

To use neovim as your editor you can add the following command to your .bashrc: `module load nvim`. This will create a fully-fledged neovim config for you and add the `nvim` executable to your `$PATH`. You can modify your configuration to your liking in `~/.modules/nvim/0.9.5/env/.config/nvim`.

[Link to Neovim presentation by Antoine](https://axeleraai-my.sharepoint.com/personal/rodrigo_borges_axelera_ai/_layouts/15/stream.aspx?id=%2Fpersonal%2Frodrigo%5Fborges%5Faxelera%5Fai%2FDocuments%2FOpnamen%2FNeovim%5F%20improve%20your%20productivity%2D20240207%5F110125%2DMeeting%20Recording%2Emp4&referrer=StreamWebApp%2EWeb&referrerScenario=AddressBarCopied%2Eview) (Access managed by [Rodrigo Borges](mailto:rodrigo.borges@axelera.ai))

### VSCode

Useful resouces:
1. [Random Visual Studio Code tips](https://axeleraai.atlassian.net/wiki/spaces/SOFTWARE/pages/26935306/Random+Visual+Studio+Code+tips)
2. [Hetzner How-To](https://doc.axelera.ai/ai-hw-team/triton/user_guides/hetzner_howto/)


#### Remote Development using SSH

It might be more convenient to keep working from the VS Code instance on your local machine (eg. Windows) instead of connecting to the Hetzer machine via something like TigerVNC. To do that, `Remote-SSH` extension can be utilized and IP and VNC password of the Hetzer machine provided to it. To achieve this, steps from [Connect to a remote host](https://code.visualstudio.com/docs/remote/ssh#_connect-to-a-remote-host) can be followed.


#### Installing Extensions on Hetzer Machines

Extensions that can be installed for VS Code on Hetzer machines are located in `/opt/installers/vscode/`.

A single extension can be installed by:

```bash
code --install-extension /opt/installers/vscode/<name-of-an-extension>.vsix
````

Also, the extensions can be installed via GUI of the VS Code:

1. View: Extensions command (Ctrl+Shift+X).
2. Go to ellipsis (...) and "Install from VSIX..."
3. Paste the absolute path to the plugin or select the desigred extensions in the case GUI pops up.


## Simulation tools

### Job dispatch

If you want to run resource-heavy jobs, i.e. testbench build, test compilation and test run, you have to dispatch them on more powerful machines with the `srun` command. Otherwise you will slow down everybody on htz1. Check in the project documentation to see whether the build scripts already take care of the dispatch.

For example, to build a test with ninja, the command would look like this:

```bash
    srun -c 8 ninja <test_name> # Instruct srun to use 8 cores with the option '-c 8'
```

### Veloce usage

To launch a test on the Veloce, follow these steps:
- `cd` in the project you want to run on the emulator.
- Perform the steps described in Chapter "Usage" of the [documentation](https://ai-hw-team.doc.axelera.ai/triton/user_guides/emulation). Note: repo setup can be sped up by copying some of Antoine's functions in `/home/amdec/.bashrc.local`.
- Copy one the release builds into your project
- Run your test

Tips:
- You can see the veloce's occupation with `./run -s`.
- In case you have local modifications to do, you can either make them directly on the Veloce server, or do them on htz1 and use `rsync`. For example, the following command will sync all C files between htz1 and the veloce:
```bash
    rsync -avzm --include="*/" --include="*.c" --include="*.h" --exclude="*" /path/to/your/test/dir/on/htz1 10.4.1.10:/path/to/your/test/dir/on/veloce/server
```
