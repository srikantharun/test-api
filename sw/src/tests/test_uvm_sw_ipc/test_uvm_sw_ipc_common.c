#include <asm.h>
#include <printf.h>
#include <string.h>
#include <testutils.h>
#include <util.h>
#include <uvm_ipc/uvm_sw_ipc.h>

int test_uvm_sw_ipc_mem(void *arg) {
  UNUSED(arg);
  testcase_init();

  __attribute__((aligned)) char m1[16];
  __attribute__((aligned)) char m2[16];

  // memset
  uvm_sw_ipc_memset(&m1, 0xaa, 16);
  asm("fence");
  for (size_t i = 0; i < 16; i++) {
    CHECK_EQUAL_HEX(0xaa, m1[i], "uvm_sw_ipc_memset failed");
  }

  // memcpy
  uvm_sw_ipc_memcpy(&m2, &m1, 16);
  asm("fence");
  for (size_t i = 0; i < 16; i++) {
    CHECK_EQUAL_HEX(m1[i], m2[i], "uvm_sw_ipc_memcpy failed");
  }

  CHECK_TRUE(uvm_sw_ipc_memcmp(&m1, &m2, 16) == 0, "uvm_sw_ipc_memcmp failed");

  m1[4] = 0;
  asm("fence");
  CHECK_TRUE(uvm_sw_ipc_memcmp(&m1, &m2, 16) < 0, "uvm_sw_ipc_memcmp failed");

  m1[3] = 0xff;
  asm("fence");
  CHECK_TRUE(uvm_sw_ipc_memcmp(&m1, &m2, 16) > 0, "uvm_sw_ipc_memcmp failed");

  return testcase_finalize();
}

int test_uvm_sw_ipc_printf() {
  uvm_sw_ipc_print_info(0, "Starting test.");

  uint32_t a = 69;
  double b = 420.00;
  printf("Hello Verif Team <3. This is the UVM printf!\n");
  printf("Test: one=%d\n", 1);
  printf("Test: two=%03d\n", 2);
  printf("Test: three=%u\n", 3);
  printf("Test: deadbeefs=%lxs\n", 0xDEADBEEFuL);
  printf("Test: pi=%f\n", 3.14159);
  printf("Test: string='%s'", "This is a string. =)\n");
  printf("Test: two chars='%c%c'\n", '=', ')');
  printf("Test: two numbers with weird sep='0x%03x~/%f'\n", a,b);
  printf("Test: this is a pointer address: %p'\n", &a);

  return 0;
}

// test description:
//   2. execute the run_test() at the same time, using their own memory to
//   communicate with UVM
//   3. UVM - fw_test_uvm_sw_ipc_sanity: checks the data is correct
//   4. ask simulation to stop and prints UVM report
int test_uvm_sw_ipc_sanity_hdl(const char *reg_path) {
  testcase_init();

  uvm_sw_ipc_print_info(0, "run_hdl_test");

  uint64_t wdata;
  uint64_t rdata;

  // deposit
  rdata = uvm_sw_ipc_hdl_read(reg_path);
  uvm_sw_ipc_print_info(2, "%0s = 0x%x", reg_path, rdata);

  wdata = (r_mhartid() << 32) | 0xdeadbeef;
  uvm_sw_ipc_print_info(2, "deposit %0s = 0x%x", reg_path, wdata);
  uvm_sw_ipc_hdl_deposit(reg_path, wdata);

  rdata = uvm_sw_ipc_hdl_read(reg_path);
  uvm_sw_ipc_print_info(2, "%0s = 0x%x", reg_path, rdata);
  CHECK_EQUAL_INT(wdata, rdata, "uvm_sw_ipc_hdl_deposit failed");

  // do not test uvm_sw_ipc_hdl_force() since it requires -debug_access+f,
  // which can make the simulations twice as long
  return testcase_finalize();
}

int test_uvm_sw_ipc_sanity_synchronization(void *arg) {
  UNUSED(arg);

  uint64_t data_arr[2] = {0};
  uint64_t data;
  uint64_t i;

  uvm_sw_ipc_print_info(1, "gen event 0x%0x", 16);
  uvm_sw_ipc_gen_event(16);

  uvm_sw_ipc_print_info(0, "wait event 1");
  uvm_sw_ipc_wait_event(1);
  i = 0;
  while (i < 2 && uvm_sw_ipc_pull_data(0, &data)) {
    data_arr[i] = data;
    i++;
  }
  uvm_sw_ipc_push_data(0, data_arr[0]);
  uvm_sw_ipc_push_data(0, data_arr[1]);
  uvm_sw_ipc_gen_event(0);

  uvm_sw_ipc_print_warning(0, "bye bye");
  return 0;
}
