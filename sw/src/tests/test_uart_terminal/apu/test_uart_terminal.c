// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

// description: test ./uart by printing what you type. Type 'exit' to finish

#include <printf.h>
#include <uart/drv_uart.h>

int main(){
  char command[4];
  int char_index = 0;

  printf("test ./uart by printing what you type. Type 'exit' to finish\n");
  while (1) {
    // print char
    char c;
    c = readSerial();
    writeSerial(c);

    // return on exit command
    if ((char_index < 4) && c != '\n') {
      command[char_index] = c;
      char_index++;
      if (strcmp("exit",command) == 0) {
        printf("\nEXIT: exiting test\n");
        return 0;
      }
    } else {
      char_index = 0;
    }
  }
  return 1;
}
