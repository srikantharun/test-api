// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// Package with delay sequeces to allow soc mgmt reset prperties to support
// variable delays
// This code is copied from here. <https://verificationacademy.com/forums/t/assertion-with-variable-declaration-in-sva/35404/2
//
package sva_delay_repeat_pkg;
  sequence dynamic_repeat(q_s, count);
    int v=count;
    (1, v=count) ##0 first_match((q_s, v=v-1'b1) [*1:$] ##0 v<=0);
  endsequence
 
  sequence dynamic_delay(count);
    int v;
    (1, v=count) ##0 first_match((1, v=v-1'b1) [*0:$] ##1 v<=0);
  endsequence
endpackage
