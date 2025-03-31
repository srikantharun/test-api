
#include "include/secure_ip_hal.h"

int secure_ip_open()
{
    return 0;
}

void secure_ip_close()
{
}

/* Physical base address where the FemtoRoT AHB bus is mapped */
const uint32_t BASE = 0x40000000;

/* Write a 32-bit value to a physical address */
void write_reg32( size_t offset, uint32_t value )
{
    *((volatile uint32_t*)offset) = value;
}


/* Read a 32-bit value from a physical address */
uint32_t read_reg32( size_t offset )
{
    return *((volatile uint32_t*)offset);
}


/* Write bytes to a physical address */
void write_bytes( size_t offset, uint8_t* buffer, uint32_t length )
{
    uint8_t* dest = (uint8_t*)offset;
    memcpy( dest, buffer, length );
}


/* Read bytes from a physical address */
void read_bytes( size_t offset, uint8_t* buffer, uint32_t length )
{
    uint8_t* src= (uint8_t*)offset;
    memcpy( buffer, src, length );
}


/* Process a command, including polling and status retrival */
uint8_t execute( uint8_t token, uint16_t sub_cmd )
{
    uint32_t ctrl;
    uint8_t status;
    uint32_t trk;
    //uint32_t perf;

    //start the command
    write_reg32(ADDR_CMD_CTRL, (uint32_t)token << 24 | sub_cmd << 8 | 1);

    //wait command done
    do {
        ctrl = read_reg32(ADDR_CMD_CTRL);
    } while (ctrl & 1);

    //clear interrupt
    write_reg32(ADDR_INT_CTRL, 0x0);

    //check satus
    status =  read_reg32(ADDR_CMD_STATUS) & 0xFF;
    if (status != KSE3_SUCCESS) {
    //    printf("unexpected comand status 0x%02X\n", status);
        return status;
    }

    // check tracker
    trk = read_reg32(ADDR_CMD_TRK);
    if (trk != (~(ctrl) | 0x000000FF)) {
        printf("unexpected comand tracker 0x%02X\n", trk);
        return 2;
    }

    //check performance (commented because the info is not used)
    //perf = read_reg32(ADDR_CMD_PERF);

    return status;
}


/* Perform a reset */
void reset()
{
  //clear interrupt that is generated at reset
  write_reg32(ADDR_INT_CTRL, 0x0);
}

/* log to a file not available in bare metal */
void log_open(const char *filename) {
  UNUSED(filename);
}
void log_close() {}


/* End of file */
