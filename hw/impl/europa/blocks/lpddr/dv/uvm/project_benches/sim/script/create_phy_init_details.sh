#!/bin/sh

create_struct () {
  in_file_name="$1"
  struct_name="$2"
  out_file_path="$3"
  # Extracting required details from output txt files to a temporary file
  grep -P -B 1 "Start of .*_[A-K]_|End of.*_[A-K]_|dwc_ddrphy_apb_wr|dwc_ddrphy_phyinit_userCustom_wait" $in_file_name > temp_file.sv
  sed -i ":a;N;\$!ba;s/--\n//g" temp_file.sv

  # reformatting Temporary file details in an SV Multidimential Struct Array
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]*\)\n\(dwc_ddrphy_apb_wr[^\n]*\)\n/\2 \1\n/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]*\)\n\(dwc_ddrphy_phyinit_userCustom_wait[^\n]*\)\n/\2\n/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* End of[^\n]*\)\n/\1\n\n/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]*\)\n\(\/\/[^\n]* Start of[^\n]*\)\n/\2\n/g" temp_file.sv
  sed -i "s/dwc_ddrphy_apb_wr(\(.*\),\(.*\));/                          '{ step_type : REG_WRITE, reg_addr : \1, value : \2},/" temp_file.sv
  sed -i "s/dwc_ddrphy_phyinit_userCustom_wait(\(.*\));/                          '{ step_type : WAIT_DFI, reg_addr : 0, value : \1},/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* End of[^\n]*\)\n/\1\n\n/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]*\)\n\(\/\/[^\n]* Start of[^\n]*\)\n/\2\n/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/\n[\n]*/\n/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_A_[^\n]*\)\n/ const phy_init_data_t $struct_name[string][] = '{\n   \"A\" : '{                 \n\1\n/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([B]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([C]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([D]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([E]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([F]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([G]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([H]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([I]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/\(\/\/[^\n]* Start of[^\n]*_\([J]\)_[^\n]*\)\n/   },\n   \"\2\" : '{                 \n\1\n/" temp_file.sv
  sed -i ":a;N;\$!ba;s/},\([^{^}]*  },\)/}\1/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/  \"[A-J]\" : '{\([^{^}]*\)  },/\1/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/  \"[A-J]\" : '{\([^{^}]*\)  }/\1/g" temp_file.sv
  echo "   }" >> temp_file.sv
  echo "};" >> temp_file.sv
  sed -i ":a;N;\$!ba;s/  \"[A-J]\" : '{\([^{^}]*\)  },/\1/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/  \"[A-J]\" : '{\([^{^}]*\)  }/\1/g" temp_file.sv
  sed -i ":a;N;\$!ba;s/},\([^{^}]*};\)/}\1/g" temp_file.sv
  cat temp_file.sv > $out_file_path/$struct_name.sv 
  rm -rf temp_file.sv

}

create_struct $1/dwc_ddrphy_phyinit_out_lpddr5_skiptrain.txt phy_init_skiptrain_details $2
create_struct $1/dwc_ddrphy_phyinit_out_lpddr5_devinit_skiptrain.txt phy_init_devinit_skiptrain_details $2
create_struct $1/dwc_ddrphy_phyinit_out_lpddr5_train.txt phy_init_train_details $2
