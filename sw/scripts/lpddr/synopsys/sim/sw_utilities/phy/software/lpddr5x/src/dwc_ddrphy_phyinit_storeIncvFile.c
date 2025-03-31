/**
 * \file
 * \brief Reads firmware image incv file
 * \addtogroup SrcFunc
 * @{
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "dwc_ddrphy_phyinit.h"

/** \brief Reads firmware image incv file
 *
 * Routine to read an incv file into an internal mem array.
 *
 * \return the address of the first apb write in the incv file to use as the mem
 * offset.
 */
int dwc_ddrphy_phyinit_storeIncvFile(char *incv_file_name, uint32_t mem[], return_offset_lastaddr_t return_type)
{
	FILE *incvfile_ptr;
	char *p;
	char instr[255];
	int raw;
	uint32_t adr, x, first, offset = 0;
	uint32_t dat;

	// die if can't open incv file
	// coverity[misra_c_2012_rule_21_6_violation]
	incvfile_ptr = fopen(incv_file_name, "r");
	if (incvfile_ptr == NULL) {
		dwc_ddrphy_phyinit_assert(0, " [%s] Error:  Error opening input file %s/\n\n", __func__, incv_file_name);
	}
	else {
		dwc_ddrphy_phyinit_cmnt(" [%s] Reading input file: %s\n\n", __func__, incv_file_name);
	}

	// assume entire incv file is made of lines that look like
	// apb_wr(32'haaaa,32'hdddddddd);
	// and capture the aaaa and dddd values to load array

	first = 0;
	adr = 0;
	// coverity[misra_c_2012_rule_21_6_violation]
	while (fgets(instr, 255, incvfile_ptr) != NULL) {
		p = strtok(instr, "(");
		x = 0;
		do {
			p = strtok(NULL, "h,)");
			if (p) {
				if (x == 1) {
					// coverity[misra_c_2012_rule_21_6_violation]
					sscanf(p, "%x", &raw);
					adr = (uint32_t)raw;
				}
				else if (x == 3) {
					// coverity[misra_c_2012_rule_21_6_violation]
					sscanf(p, "%x", &raw);
					dat = (uint32_t)raw;
					if (first == 0) {
						offset = adr;
						first = 1;
					}
					mem[adr - offset] = dat; // load array
				}
				else {
					// do nothing (else statement added for MISRA-C compliance)
				}
			}
			x++;
		} while (p);
	}
	// coverity[misra_c_2012_rule_21_6_violation]
	fclose(incvfile_ptr);

	if (return_type == return_lastaddr) {
		offset = adr; //return the last addr
	}

	return offset;
}

/** @} */
