#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Mar 10 16:09:24 2022

@author: spyridoulakoumousi

Python 3 Program to convert a given decimal number into
Gray code form and extract the min and max indeces that satisfy
a single bit toggle when the counter wraps around.

"""

import argparse
import pandas as pd


def numBits(dec_data):
    """
      Return the number of bits needed to represent
      a decimal number in binary format

    """
    k = 0
    while dec_data > 2**k:
        k+=1
    return k


def dec2bin(dec_data, num_bits):
    """
      Convert a decimal number to binary and
      extend it to the needed number of bits

    """
    scale = 10
    data = bin(int(dec_data, scale))[2:].zfill(num_bits)
    return data


def grayCode(n):
    """
      Convert a decimal number to the decimal
      representation of the Gray code

    """
	# Right Shift the number by 1 taking xor with
	# original number
    return n ^ (n >> 1)

def grayCodeBin(n,num_bits):
    """
     Calculate the Gray Decimal value and convert it
    to binary

    """
    return dec2bin(str(grayCode(n)),num_bits)


def nearestPow2(n):
    """
     Find the nearest lowest power of 2 number for
     an integer number 'n'

    """
    i = 0
    while 2**i <n:
        i +=1
    return 2**(i-1)

def findMinIndex(n):
    """
     Find the nearest lowest power of 2 number for
     an integer number 'n'

    """
    nearPow2 = nearestPow2(n)
    distFromPow2 = n - nearPow2
    idxMin = n/2 - distFromPow2
    return int(idxMin)

def printGrayRange(
    n: int,
    fifo_depth: int,
    verbose: bool,
):
    dec_data = []
    bin_data =[]
    gray_data = []
    gray_indecimal = []

    num_bits = numBits(n)
    for i in range (0,n):
        dec_data.append(i)
        bin_data.append(dec2bin(str(i),num_bits))
        gray_data.append(grayCodeBin(i,num_bits))
        gray_indecimal.append(grayCode(i))
    df= pd.DataFrame({"Decimal":dec_data,"Binary":bin_data,  "Gray": gray_data, "Gray in decimal":gray_indecimal })
    res = 0

    idx_min = 0
    idx_max = 0

    while res != 1:

        idx_max = idx_min + fifo_depth - 1
        res = str(bin(df.iloc[idx_min]['Gray in decimal'] ^ df.iloc[idx_max]['Gray in decimal'])).count('1')
        idx_min = idx_min + 1

    if verbose:
        with pd.option_context('display.max_rows', None, 'display.max_columns', None):
            print(df.iloc[idx_min-1:idx_max+1])

    return idx_min-1, idx_max



if __name__ == "__main__":


    parser = argparse.ArgumentParser()
    parser.add_argument("--fifo_depth",  metavar="fifo_depth",
                      help="Please provide the FIFO depth needed: -fifo_depth 6")

    parser.add_argument("-v", action="store_true", dest="verbose",default=False)

    args = parser.parse_args()

    # Calculate the starting index for the Gary coding counting
    fifo_depth = int(args.fifo_depth)
    idx_min = findMinIndex(fifo_depth)
    idx_max = idx_min + fifo_depth - 1
    print("FIFO depth =", str(fifo_depth) +" Condition satisfied for min index: "+ str(idx_min)  + " and max index: "+ str(idx_max))

    # Validation - extract the index from the table and check if they match
    # Max value could be an arbitrary high value - it is just used to ensure there is enough gray numbers
    # to find the right min and max index combination to ensure that for any even number of fifo depth
    # the gray counter wraps around with a single bit toggle. d
    max_value = 2**fifo_depth
    idx_min_val ,idx_max_val =  printGrayRange(max_value,fifo_depth, args.verbose)

    # Assert the two min indeces match
    # Max indeces should match by defaul as they are a function of min index and fifo_depth
    assert (idx_min == idx_min_val) , "Min indeces do not match"
    assert (idx_max == idx_max_val) , "Max indeces do not match"
