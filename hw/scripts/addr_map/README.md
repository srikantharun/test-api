## Generate the address map

Currently the address map script only supports the Europa project.
The paths inside the script are set to the default locations of the Europa paths. 
The script will be refactored once we move towards Titania. 

### Address map generation/update
If changes have been applied to the Europa address map file you can re-generate the address map files using the following command from any location within the project:

```bash
addrmap render -c hw/impl/europa/data/memory_map/memory_map.yml
```

### Address location in the memory map

A unit functionality has been added in the address map generation script to enable engineers to easily understand where an address is located within the memory map.
Using the following command and by formatting the address as in the below example you can easily get info on the address:

```bash
addrmap  info -a 0x0001_1111  -c ./hw/impl/europa/data/memory_map/memory_map.yml
```

This will output the following info:


```bash
"The address 0x0001_1111 is in the APU - Boot ROM region." 
```

For any issues, bugs please report to Spyridoula Koumousi @spyridoula.koumousi@axelera.ai
