# Configuration for the IP
IP_NAME            = dma
TOP_LEVEL_MODULES  = tb
BENDER_MANI_LOC    = .
UVM                = 1
TESTNAME           = dma_base_test
SEED               = 1

override GLOBAL_DEFINES += +define+DMA_NCHANNELS=4
