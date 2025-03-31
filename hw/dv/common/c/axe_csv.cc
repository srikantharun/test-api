// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:  Axelera CSV Logger
// Generic and flexible CSV file generation using DPI
// Owner: Andy Bond

#include <iostream>
#include <fstream>
#include <map>
#include <stdarg.h>
#include "svdpi.h"


namespace axe_csv {

    std::map<std::string, std::fstream> fmap;

    std::fstream *open_file(const char *filename, const char *hdr) {
        if (fmap.count(filename) == 0) {
            fmap[filename].open(filename, std::ios::out | std::ios::trunc);
            fmap[filename] << hdr << "\n";
            fmap[filename].flush();
        } else if (!fmap[filename].is_open()) {
            fmap[filename].open(filename, std::ios::out | std::ios::app);
        }
        return &(fmap[filename]);
    }

    void close_file(std::fstream *h) {
        if (h == NULL) {
            for (auto it = fmap.begin(); it != fmap.end(); ++it) {
                close_file(&it->second);
            }
        } else {
            if (h->is_open()) {
                h->close();
            }
        }
    }

    void write(std::fstream *h, const svOpenArrayHandle sv_array) {
        if (sv_array == NULL) {
            printf("ERROR: NULL array received.\n");
            return;
        }


        // Get the size of the array (1st dimension)
        int array_size = svSize(sv_array, 1);

        for (int i = 0; i < array_size; i++) {
            // Access each string using svGetArrElemPtr1
            const char* sv_str = *(const char**)svGetArrElemPtr1(sv_array, i);
            if (sv_str != NULL) {
                (*h) << sv_str;
            }
            if (i < array_size -1 ) {
                (*h) << ",";
            }
         }
         (*h) << "\n";
         h->flush();
    }
}


extern "C" {
    void *open_csv(const char *filename, const char *hdr) {
        std::fstream *h = axe_csv::open_file(filename, hdr);
        return reinterpret_cast<void*>(h);
    }

    void close_csv(void *h) {
        axe_csv::close_file(reinterpret_cast<std::fstream*>(h));
    }

    void write_csv(void *h, const svOpenArrayHandle sv_array) {
        axe_csv::write(reinterpret_cast<std::fstream*>(h), sv_array);
    }
}
