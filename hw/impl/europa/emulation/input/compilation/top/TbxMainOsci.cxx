//--------------------------------------------------------------------------//
// Siemens EDA                                                              //
// Unpublished work. (C) Copyright 2021 Siemens                             //
//                                                                          //
// This material contains trade secrets or otherwise confidential           //
// information owned by Siemens Industry Software Inc. or its affiliates    //
// (collectively, "SISW"), or its licensors. Access to and use of this      //
// information is strictly limited as set forth in the Customer's           //
// applicable agreements with SISW.                                         //
//                                                                          //
// This material (reprints of pages, PDFs, complete code examples) may not  //
// be copied, distributed, or otherwise disclosed outside of the Customer’s //
// facilities without the express written permission of SISW, and may not   //
// be used in any way not expressly authorized by SISW.                     //
//--------------------------------------------------------------------------//

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <vector>
#include <string>
#include <dlfcn.h>

using namespace std;

#include "systemc.h"
#include "svdpi.h"
#include "svdpi_src.h"
#include "tbxsyscmanager.hxx"

static TbxSyscManager *tbx = NULL;

//---------------------------------------------------------
// This is a implementation function acc_product_version for use with
// TBX. It is created so that code that calls acc_product_version()
// (which is useful for specifying initial breakpoints in gdb), will
// work in either native MTI mode (where acc_product_version() is natively
// defined), or TBX.
//===========================================================================

extern "C" {

char *acc_product_version(void){ return "OSCI-SystemC-XL"; }

} /* extern "C" */

//---------------------------------------------------------
// errorHandler()                            johnS 1-5-2004
//
// This error handler is registered with the TBX infrastructure
// to handle all exception conditions. When an exception occurs
// in TBX, this function is automatically called. It then
// throws a string exception which is caught at one of the
// root SystemC threads.
//---------------------------------------------------------

static void errorHandler( void */*context*/, SceMiEC *ec ) {
    char buf[128];
    sprintf( buf, "%d", (int)ec->Type );
    string messageText( "TBX Error[" );
    messageText += buf;
    messageText += "]: Function: ";
    messageText += ec->Culprit;
    messageText += "\n";
    messageText += ec->Message;
    fprintf( stderr, "%s\n", messageText.c_str() );
    throw messageText;
}

#ifndef TBX_RAWC_OSCI
extern void tbxMain( int argc, char *argv[] );
#endif // TBX_RAWC_OSCI

//____________________                                      _________________
// class Bootstrapper \____________________________________/ johnS 10-23-2008
//---------------------------------------------------------------------------

class Bootstrapper : public sc_module {
  private:
    vector<string> bootstrapLibs;
       vector<string> bootstrapSymbols;
    vector<void (*)()> bootstrapAddresses;

  public:
    Bootstrapper( sc_module_name name ) : sc_module(name) { }

    void start_of_simulation(){
        for( unsigned i=0; i<bootstrapAddresses.size(); i++ )
            (*bootstrapAddresses[i])();
    }

    //---------------------------------------------------------
    // ::scanArgs()
    // 
    // Scan main args for +bootstrap+<shared lib>.so+<function name>
    // bootstrap entrypoints.
    //
    // Call any bootstrap functions encountered.
    //---------------------------------------------------------

    void scanArgs( int argc, char *argv[] ){

        unsigned i, j;
        string option, value0, value1;

        printf( "INFO: Bootstrapper is scanning argc/argv[] list ...\n" );

        for( i=1; i<(unsigned)argc; i++ )
            if( argv[i][0] == '+' ){
                unsigned char c;
                option = value0 = value1 = "";
                for( j=1; (c=argv[i][j]) && c != '+'; j++ ) option += c;
                if( c == '+' )
                    for( ++j; (c=argv[i][j]) && c != '+'; j++ ) value0 += c;
                if( c == '+' )
                    for( ++j; (c=argv[i][j]); j++ ) value1 += c;
                if( option == "bootstrap" && value1 != "" ){
                    bootstrapLibs.push_back( value0 );
                    bootstrapSymbols.push_back( value1 );
                }
            }

        // Attempt to call each of the bootstrap functions identified
        // in the main args.
        for( i=0; i<bootstrapLibs.size(); i++ ){
            void *dlHandle = dlopen( bootstrapLibs[i].c_str(), RTLD_NOW );

            if( dlHandle == NULL ){
                fprintf( stderr,
                    "ERROR: dlopen() failure '%s' while trying to load "
                    "shared library %s\n",
                    dlerror(), bootstrapLibs[i].c_str() );
            }
            else {
                bootstrapAddresses.push_back( (void (*)())dlsym(
                    dlHandle, bootstrapSymbols[i].c_str() ) );

                const char *error = dlerror();

                if( error )
                    fprintf( stderr,
                        "ERROR: dlsym() failure '%s' while trying to load "
                        "symbol %s from shared library %s\n",
                        error,
                        bootstrapSymbols[i].c_str(),
                        bootstrapLibs[i].c_str() );

                else {
                    printf( "INFO: ::scanArgs() found bootstrap entry bootstrapLibs[%d]=%s bootstrapSymbols[%d]=%s bootstrapAddresses[%d]=%p\n",
                       i, bootstrapLibs[i].c_str(),
                       i, bootstrapSymbols[i].c_str(),
                       i, bootstrapAddresses[i] );
                }
            }
            dlerror(); // Clear previous errors;
        }
    }
};

//---------------------------------------------------------
// sc_main()                                 johnS 1-5-2004
//
// This is the SystemC "main()" from which all else happens.
//---------------------------------------------------------

int sc_main( int argc, char *argv[] ){
    // Register error handler with the TBX SystemC manager.
    TbxSyscManager::RegisterErrorHandler( errorHandler, NULL );

    try {
        tbx = new TbxSyscManager("tbx", argc, argv);

#ifdef TBX_RAWC_OSCI
        Bootstrapper bootstrapper( "bootstrapper" );

        bootstrapper.scanArgs( argc, argv );
#else
        /////tbxMain( argc, argv );
#endif // TBX_RAWC_OSCI

        // Kick off SystemC kernel ...
        sc_start();

        delete tbx; // Delete TBX manager
    }
    catch( string message ) {
        cerr << message << endl;
        cerr << "Fatal Error: Program aborting." << endl;
        if( tbx ) delete tbx;
        return -1;
    }
    catch(sc_report message) {
        cout << "Error: SystemC report:" << endl;
        cout << "Type: "        << message.get_msg_type() << endl;
        cout << "Message: "     << message.get_msg() << endl;
        cout << "Severity: "    << message.get_severity() << endl;
        cout << "Where: line #" << message.get_line_number()
             << " in "          << message.get_file_name() << endl;
        cout << "Fatal Error: Program aborting." << endl;
        if( tbx ) delete tbx;
        return -1;
    }
    catch(sc_exception message) {
        cerr << "Error: SystemC exception:" << endl;
        cerr << message.what() << endl;
        cerr << "Fatal Error: Program aborting." << endl;
        if( tbx ) delete tbx;
        return -1;
    }
    catch(...) {
        cerr << "Error: Unclassified exception." << endl;
        cerr << "Fatal Error: Program aborting." << endl;
        if( tbx ) delete tbx;
        return -1;
    }

    return 0;
}

#define SC_MODULE_EXPORT( tb ) \
SC_MODULE_EXPORT( tb ) \
    void tbxMain( int argc, char *argv[] ){ \
        tb *myTestbench = new tb( "myTestbench" ); \
        static void *gccnowarn = &gccnowarn + (long)myTestbench; \
    }
//--------------------------------------------------------------------------//
 // Unpublished work. Copyright 2021 Siemens
 // 
 // This material contains trade secrets or otherwise confidential information
 // owned by Siemens Industry Software Inc. or its affiliates (collectively,
 // "SISW"), or its licensors. Access to and use of this information is strictly
 // limited as set forth in the Customer's applicable agreements with SISW.  
//--------------------------------------------------------------------------//
////#include "config.h"
////#include "FlexMem.h"

//SC_MODULE_EXPORT(FlexMem_dfi_lpddr4);
