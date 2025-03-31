// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Resource Allocators
// Resource allocator to ensure unique ranges for independent threads
// Owner: abond

// Package: axe_uvm_resource_alloctor_pkg
package axe_uvm_resource_allocator_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;

  // Allocation policy
  // ALLOCATE_FRONT  : Allocate from front of resource pool
  // ALLOCATE_BACK   : Allocate from back of resource pool
  // ALLOCATE_RANDOM : Allocate randomly from resource pool 
  typedef enum {ALLOCATE_FRONT, ALLOCATE_BACK, ALLOCATE_RANDOM} resource_allocation_policy_t;

  `include "axe_uvm_resource_allocator.svh"
  `include "axe_uvm_memory_allocator.svh"

endpackage : axe_uvm_resource_allocator_pkg
