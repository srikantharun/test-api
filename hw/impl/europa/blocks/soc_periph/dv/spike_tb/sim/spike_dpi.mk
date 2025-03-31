SPIKE_DPI_DIR := $(REPO_ROOT)/hw/dv/spike_dpi

DPI_C_SRC += $(SPIKE_DPI_DIR)/cpp/dpi_device.cpp $(SPIKE_DPI_DIR)/cpp/preloaded_sim.cpp
DPI_C_INCDIR += $(SPIKE_HOME)/include/ \
                $(SPIKE_HOME)/include/riscv \
                $(SPIKE_DPI_DIR)/cpp \
                $(REPO_ROOT)/sw/src/lib/ # Enable us to include memorymap.h


DPI_C_OPTS += -Wl,-rpath=$(SPIKE_HOME)/lib \
              -L$(SPIKE_HOME)/lib \
              -lriscv \
              -DARCH=64

ifeq ($(DEBUG), 1)
DPI_C_OPTS += -DDUMP_INST
endif
