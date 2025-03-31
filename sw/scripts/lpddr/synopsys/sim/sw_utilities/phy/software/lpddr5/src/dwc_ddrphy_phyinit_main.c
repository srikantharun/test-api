
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <errno.h>
#include "dwc_ddrphy_phyinit.h"
#include "dwc_ddrphy_phyinit_LoadPieProdCode.h"

FILE *outFilePtr;     //defined in phyinit.h file
char *CmntStr = "";   //defined in phyinit.h file
char *ApbStr = "";    //defined in phyinit.h file

/** \file
 *  \brief Main function for phyinit executable
 *  \addtogroup SrcFunc
 *  @{
 */

/** \brief Main function of PhyInit standalone executable.
 *
 * Only used for the purpose of generating output.txt file. Parses input
 * arguments and makes a call to dwc_ddrphy_phyinit_sequence(for single PHY instance)
 *
 *  ### Required Arguments
 *
 *  - output filename
 *	- filename of the output txt file.
 *
 *  - skip_train <0|1|2>
 *	- if set to 0 firmware training is executed.
 *	- if set to 1 training is skipped and registers are programmed to work with
 *	  zero board delay.
 *	- if set to 2 training is used to skip training but execute the firmware to
 *	  initialize the DRAM state while registers are programmed to work with zero
 *	  board delay.
 *
 *  #### Optional Arguments
 *
 *  - debug \<level\>
 *	- useful for generating additional print statements for debug purpose.
 *	  Currently only level must be 0. default=0.
 *
 *  - comment_string
 *	- a custom comment string to place on non-system verilog compatible lines in
 *	  the output txt files. default is an empty string.
 *
 *  - apb_string
 *	- a custom comment string to place on register write commands in
 *	  the output txt files. default is an empty string.
 *
 *  - retention_exit
 *	- if set to 1 creates additional output_retention_exit.txt file with sequence for IO retention exit.
 
 * Example: generating output txt file for 1D/2D training.
 * \code{.sh}
 * phyinit -skip_train 0
 * \endcode
 *
 * @param argc number of input arguments.
 * @param argv char array of input arguments.
 */
int main2(int argc, char *argv[])
{
	// Allocate configuration structure
	static phyinit_config_t phyConfig;

	int skip_train = -1;
	int train2d = 0;
	int debug = 0;
	int retExit = 0;
	uint32_t pubRev = 0;
	char *pllSettings = NULL;
	int i;
	char outFileName[256] = { '\0' };
	char *Usage = "\n \
	phyinit executable\n \
	\n \
	This executable will generate a txt file output with register write instructions\n \
	to initialize the Synopsys DWC_DDRPHY phy.\n \
	phyinit <required arguments> [options]\n \
	\n \
	<required arguments>\n \
	-output filename\n \
		filename of the output txt file.\n \
	\n \
	-skip_train <0|1|2>\n \
		if set to 0 firmware training is executed.\n \
		if set to 1 training is skipped and registers are programmed to work with\n \
		zero board delay.\n \
		if set to 2 training is used to skip training but execute the firmware to\n \
		initialize the DRAM state while registers are programmed to work with zero\n \
		board delay.\n \
\n \
	[optional arguments]\n \
	-debug <level>\n \
		useful for generating additional print statements for debug purpose.\n \
		Currently only level must be 0.\n \
\n \
	-comment_string\n \
		a custom comment string to place on non-system verilog compatible lines in\n \
		the output txt files. default is an empty string.\n \
\n \
	-pll_settings_file \n \
        	a path to the Technology specific PLL Settings File.\n \
        	used to override default values from Phyinit. default is an empty string.\n \
        	BETA feature.\n \
\n \
	-apb_string\n \
		a custom comment string to place on register write commands in\n \
		the output txt files. default is an empty string.\n \
\n \
	- retention_exit <0|1>\n \
		if set to 1 creates additional output_retention_exit.txt file with sequence for IO retention exit.\n \
\n \
     - pub_rev <rev_num>\n \
		chooses revision of PUB digital hardware to be configured by PhyInit.\n \
\n \
     Example:\n \
	phyinit -skip_train 0 -debug 1 \n \
";
	for (i = 1; i < argc; i = i + 2) {
		if (strcmp("-skip_train", argv[i]) == 0){
			errno = 0;
			skip_train = (int) strtol(argv[i + 1], (char **)NULL, 10);
			if (0 != errno)
			{
				dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] strtol error\n");
			}
		}
		else if (strcmp("-train2d", argv[i]) == 0){
			// coverity[misra_c_2012_rule_21_6_violation]
			printf(" [dwc_ddrphy_phyinit_main] Note: the train2d option is deprecated, option ignored\n");
		}
		else if (strcmp("-debug", argv[i]) == 0){
			errno = 0;
			debug = (int) strtol(argv[i + 1], (char **)NULL, 10);
			if (0 != errno)
			{
				dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] strtol error\n");
			}
		}
		else if (strcmp("-comment_string", argv[i]) == 0){
			CmntStr = argv[i + 1];
		}
		else if (strcmp("-apb_string", argv[i]) == 0){
			ApbStr = argv[i + 1];
		}
		else if (strcmp("-pll_settings_file", argv[i]) == 0){
    		pllSettings = argv[i+1];
		}
		else if (strcmp("-retention_exit", argv[i]) == 0){
			errno = 0;
			retExit = (int) strtol(argv[i + 1], (char **)NULL, 10);
			if (0 != errno)
			{
				dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] strtol error\n");
			}
		}
		else if (strcmp("-pub_rev", argv[i]) == 0){
               errno = 0;
			pubRev = (int) strtol(argv[i + 1], (char **)NULL, 10);
			if (0 != errno)
			{
				dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] strtol error\n");
			}
          }
		else if (strcmp("-output", argv[i]) == 0){
			// coverity[misra_c_2012_rule_21_6_violation]
			snprintf(outFileName, sizeof(outFileName), "%s", argv[i + 1]);
		}
		else{
			dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] Unsupported argument %s is supplied.\n", argv[i]);
		}
	}

	if (skip_train != 0 && skip_train != 1 && skip_train != 2){
		dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] skip_train(%d) no set or invalid input. See usage.\n%s\n", skip_train, Usage);
	}

	if (outFileName[0] == '\0'){
		dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] output file not specified. See usage.\n%s\n", Usage);
	}

	if (CmntStr == NULL){
		dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] Comments String is NULL. See usage.\n%s\n", Usage);
	}

	if (ApbStr == NULL){
		dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] abp_strings is NULL. See usage.\n%s\n", Usage);
	}
	if (pubRev > 2) {   // 0,1,2 are all valid pub revisions (PUB_RID,PUB_REV,PUBREV)
		dwc_ddrphy_phyinit_assert (0," [dwc_ddrphy_phyinit_main] pub_rev unset or invalid. See usage.\n%s\n", Usage);
	}
	// coverity[misra_c_2012_rule_21_6_violation]
	printf(" [dwc_ddrphy_phyinit_main] Running with values of skip_train = %0d, debug = %0d output=%s  pubRev = 0x%04x \n", skip_train, debug, outFileName, pubRev);

	// registering function inputs
	phyConfig.runtimeConfig.skip_train = skip_train;
	phyConfig.runtimeConfig.Train2D = train2d;
	phyConfig.runtimeConfig.debug = debug;
	phyConfig.runtimeConfig.RetEn = retExit;
	phyConfig.runtimeConfig.pubRev = pubRev;
	phyConfig.runtimeConfig.pllSettings = pllSettings;

	switch (phyConfig.runtimeConfig.skip_train) {
	case 0:
		phyConfig.runtimeConfig.initCtrl = 0x00;
		break;
	case 1:
		phyConfig.runtimeConfig.initCtrl = 0x0f;
		break;
	case 2:
		phyConfig.runtimeConfig.initCtrl = 0x21;
		break; // devinit+skiptrain
	case 3:
		phyConfig.runtimeConfig.initCtrl = 0x1f;
		break;
	default:
		phyConfig.runtimeConfig.initCtrl = 0;
		break;
	}
	/*
	 * function calls to generate output files when only one PHY instance is present.
	 */
	if (DWC_DDRPHY_NUM_PHY == 1) {
		// Open Txt output Stream
		// coverity[misra_c_2012_rule_21_6_violation]
		// coverity[misra_c_2012_directive_4_14_violation]
		outFilePtr = fopen(outFileName, "w");
		if (debug == 2) {
			// coverity[misra_c_2012_rule_21_6_violation]
			printf(" [dwc_ddrphy_phyinit_main] writing output to stdout\n\n");
			// coverity[misra_c_2012_rule_22_1_violation]
			outFilePtr = stdout;
		} else if (outFilePtr == NULL) {
			dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] Error:  Can't open file for writing %s/\n\n", outFileName);
		} else {
			// coverity[misra_c_2012_rule_21_6_violation]
			printf(" [dwc_ddrphy_phyinit_main] writing output file: %s\n\n", outFileName);
		}

		dwc_ddrphy_phyinit_cmnt("[%s] Start of dwc_ddrphy_phyinit_main()\n", __func__);

		// Execute phyinit sequence
		dwc_ddrphy_phyinit_sequence(&phyConfig);
		dwc_ddrphy_phyinit_cmnt("[%s] End of dwc_ddrphy_phyinit_main()\n", __func__);
		// coverity[misra_c_2012_rule_21_6_violation]
		fclose(outFilePtr);

		if (retExit) {
			char tmp[256] = { '\0' };

			dwc_ddrphy_phyinit_cmnt("[%s] printing retention exit sequence txt files\n", __func__);
			// coverity[misra_c_2012_rule_21_6_violation]
			snprintf(tmp, sizeof(tmp), "%s_retention_exit", outFileName) < 0 ? dwc_ddrphy_phyinit_assert(0, "[dwc_ddrphy_phyinit_main] snprintf() error\n") : (void)0;
			// Open Txt output Stream
			// coverity[misra_c_2012_rule_21_6_violation]
			outFilePtr = fopen(tmp, "w");
			if (outFilePtr == NULL){
				dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] Error: Can't open file for writing %s/\n\n", tmp);
			}
			else{
				// coverity[misra_c_2012_rule_21_6_violation]
				printf(" [dwc_ddrphy_phyinit_main] writing output file: %s\n\n", tmp);
			}

			dwc_ddrphy_phyinit_cmnt("[%s] Start of dwc_ddrphy_phyinit_retention_sequence()\n", __func__);

			// Execute PhyInit retention exit sequence
			dwc_ddrphy_phyinit_restore_sequence(&phyConfig);
			dwc_ddrphy_phyinit_cmnt("[%s] End of dwc_ddrphy_phyinit_retention_sequence()\n", __func__);
			// coverity[misra_c_2012_rule_21_6_violation]
			fclose(outFilePtr);
		}
	} else if (DWC_DDRPHY_NUM_PHY < 5 && DWC_DDRPHY_NUM_PHY > 1) {
		// coverity[misra_c_2012_rule_21_6_violation]
		printf(" [dwc_ddrphy_phyinit_main] Start of multi sequence()\n");
		// Multiple PHY instances.
		dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] This release of PhyInit does not support multiple PHY instances. Please contact Synopsys Support.\n");
		// coverity[misra_c_2012_rule_21_6_violation]
		printf(" [dwc_ddrphy_phyinit_main] End of dwc_ddrphy_phyinit_multi_sequence()\n");
	} else {
		dwc_ddrphy_phyinit_assert(0, " [dwc_ddrphy_phyinit_main] invalid value for DWC_DDRPHY_NUM_PHY= %d\n", DWC_DDRPHY_NUM_PHY);
		return EXIT_FAILURE;
	}
	// coverity[misra_c_2012_rule_21_6_violation]
	fflush(stdout);
	return EXIT_SUCCESS;
}

/** @} */

