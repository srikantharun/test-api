//------------------------------------------------------------------------------
//                                                                              
//            CADENCE                    Copyright (c) 2013                     
//                                       Cadence Design Systems, Inc.           
//                                       All rights reserved.                   
//                                                                              
//  This work may not be copied, modified, re-published, uploaded, executed, or 
//  distributed in any way, in any medium, whether in whole or in part, without 
//  prior written permission from Cadence Design Systems, Inc.                  
//------------------------------------------------------------------------------
//                                                                              
//   Author                : (username)@cadence.com                              
//                                                                              
//   Date                  : $Date$
//                                                                              
//   Last Changed Revision : $LastChangedRevision$
// 
//------------------------------------------------------------------------------
//   Description                                                                
//                                                                 
//   TestBench-related macros & functions
//                                       
//------------------------------------------------------------------------------

`include "sv_macros.svh"

package tb_pkg;

  /** Reverts 8 bits in a manner intended to be optimal. */
  function bit [7:0] revert(bit[7:0] orig);
    case (orig[3:0])
      4'h0: revert[7:4] = 4'h0;
      4'h1: revert[7:4] = 4'h8;
      4'h2: revert[7:4] = 4'h4;
      4'h3: revert[7:4] = 4'hC;
      4'h4: revert[7:4] = 4'h2;
      4'h5: revert[7:4] = 4'hA;
      4'h6: revert[7:4] = 4'h6;
      4'h7: revert[7:4] = 4'hE;
      4'h8: revert[7:4] = 4'h1;
      4'h9: revert[7:4] = 4'h9;
      4'hA: revert[7:4] = 4'h5;
      4'hB: revert[7:4] = 4'hD;
      4'hC: revert[7:4] = 4'h3;
      4'hD: revert[7:4] = 4'hB;
      4'hE: revert[7:4] = 4'h7;
      4'hF: revert[7:4] = 4'hF;
    endcase

    case (orig[7:4])
      4'h0: revert[3:0] = 4'h0;
      4'h1: revert[3:0] = 4'h8;
      4'h2: revert[3:0] = 4'h4;
      4'h3: revert[3:0] = 4'hC;
      4'h4: revert[3:0] = 4'h2;
      4'h5: revert[3:0] = 4'hA;
      4'h6: revert[3:0] = 4'h6;
      4'h7: revert[3:0] = 4'hE;
      4'h8: revert[3:0] = 4'h1;
      4'h9: revert[3:0] = 4'h9;
      4'hA: revert[3:0] = 4'h5;
      4'hB: revert[3:0] = 4'hD;
      4'hC: revert[3:0] = 4'h3;
      4'hD: revert[3:0] = 4'hB;
      4'hE: revert[3:0] = 4'h7;
      4'hF: revert[3:0] = 4'hF;
    endcase
  endfunction

  function int min(input int a, input int b);
    return a < b ? a : b;
  endfunction : min

  function int max(input int a, input int b);
    return a > b ? a : b;
  endfunction : max

  typedef string stringqueue[$];

  // converts string int single element queue of strings
  function stringqueue stoq(string ins);
    stringqueue q;
	  q = {ins};
    return q;
  endfunction

  function string bool2string(bit b);
    return b ? "true" : "false";
  endfunction : bool2string
  
  // converts string int single element queue of strings
  function int CalcClockDivider(int  value);
    if (value==0) return 1;
    else          return 2*value;
  endfunction

  
  //**************************************************************************************************************  
  // PEAK RANDOMIZER 
  // provides unified distribution with poison shaped peaks
  //**************************************************************************************************************  
  // use example:
  // 
  // peak_random_cl pr;
  // pr.new(seed, min_val, max_val);
  // pr.add_peak ( min_val<=peak1<=max_val);   // add 1st peak
  // pr.add_peak ( min_val<=peak2<=max_val);   // add 2nd peak
  // ...
  // pr.add_peek ( min_val<=peakN<=max_val);   // add Nth peak
  // pr.report;                                // display configuration
  // rand = pr.get;                            // get random value
  
  class peak_random_cl;
    int bottom = 0;
    int top    = 100;
    int peaks [$];
    int seeds [$];
    int seed;
    int minpeak;
    int maxpeak;
    
    //**************************************************************************************************************  
    // initialize peek randomiser
    function new (input int _seed, input int _top, input int _bottom=0);
      assert (_bottom!=_top) else $error("peak_randomizer: class constructor called with bottom value = top value" );
    
      seed = _seed;
      
      if (_top > _bottom) begin
        bottom = _bottom;
        top    = _top;
      end else begin
        bottom = _top;
        top    = _bottom;
      end
      
      minpeak = bottom ;
      maxpeak = top;
      
    endfunction
    
    //**************************************************************************************************************
    task report;
      $display ($psprintf ("peak_randomizer: config - bottom:%d, top:%d, minpeak: %d, maxpeak:%d, peaks %p",bottom,top,minpeak,maxpeak,peaks));
    endtask
    
    //**************************************************************************************************************
    task add_peak(input int newpeak);
      assert (newpeak>=bottom) else $error("peak_randomizer: add_peek function called with peek value < randomize bottom");
      assert (newpeak<=top)    else $error("peak_randomizer: add_peek function called with peek value > randomize top");
      peaks.push_front(newpeak);
      seeds.push_front(seed);
      
      if (peaks.size==1) begin
        minpeak = newpeak;
        maxpeak = newpeak;     
      end else begin
        minpeak = (newpeak<minpeak) ? newpeak : minpeak;
        maxpeak = (newpeak>maxpeak) ? newpeak : maxpeak;
      end
      
    endtask
    
    function int get();
      int i,value;
      i=$dist_uniform(seed,0,peaks.size);
    
      if (i==0) value= $dist_uniform(seed,bottom,top);
      else      value= $dist_poisson(seeds[i-1],peaks[i-1]);
      
      if (value<bottom) return minpeak;
      if (value>top)    return maxpeak;
      return value;
    
    endfunction
    
  endclass
  
  
endpackage : tb_pkg
