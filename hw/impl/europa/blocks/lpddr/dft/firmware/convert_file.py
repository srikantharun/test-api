
##repurposed from /scratch/workspace/ferguson/dwc_ap_lpddr5x_phy_sssf5a/ss3/phy/ctb/A-2024.08/testbench/script/ate_bkdoor_proc.py

import shutil
import argparse
import tempfile
import os

def ICCMBigEndianToLittleEndianConvert(file_path):
    with open(file_path, "r") as file:
        lines = file.readlines()

    with tempfile.NamedTemporaryFile(mode='w', delete=False) as temp_file:
        temp_path = temp_file.name
        for line in lines:
            ecc_h = line[0:2]
            ecc_l = line[10:12]
            data_h = line[2:10]
            data_l = line[12:20]
            data_h_arr = bytearray.fromhex(data_h)[::-1]
            data_l_arr = bytearray.fromhex(data_l)[::-1]
            data_l_sw = ''.join(f"{n:02X}" for n in data_l_arr)
            data_h_sw = ''.join(f"{n:02X}" for n in data_h_arr)

            data_full = ecc_h + data_h_sw + ecc_l + data_l_sw + "\n"
            temp_file.write(data_full.lower())

    shutil.move(temp_path, file_path)

def DCCMBigEndianToLittleEndianConvert(file_path):
    with open(file_path, "r") as file:
        lines = file.readlines()

    with tempfile.NamedTemporaryFile(mode='w', delete=False) as temp_file:
        temp_path = temp_file.name
        for line in lines:
            ecc = line[0:2]
            data = line[2:10]
            data_sw = bytearray.fromhex(data)[::-1]
            data_sw = ''.join(f"{n:02X}" for n in data_sw)
            data_full = ecc + data_sw + "\n"
            temp_file.write(data_full.lower())

    shutil.move(temp_path, file_path)

def main():
    parser = argparse.ArgumentParser(description="Convert Big Endian to Little Endian in-place.")
    parser.add_argument("file", help="Path to the file to convert.")
    parser.add_argument("--type", choices=["ICCM", "DCCM"], required=True,
                        help="Specify the conversion type (ICCM or DCCM).")
    args = parser.parse_args()

    if args.type == "ICCM":
        ICCMBigEndianToLittleEndianConvert(args.file)
    elif args.type == "DCCM":
        DCCMBigEndianToLittleEndianConvert(args.file)

if __name__ == '__main__':
    main()
