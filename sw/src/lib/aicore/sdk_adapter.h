// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// THIS FILE IS AUTOMATICALLY GENERATED. DO NOT MODIFY.
// Use the "blueprint-engine" to regenerate this file.

/* clang-format off */

#ifndef __SDK_ADAPTER_H__
#define __SDK_ADAPTER_H__

// TODO(yruff): This is a temporary file to handle the distinctions between 
// Verification SDK and Voyager SDK.
// The mid-term goal is to align on a common interface which is clearly defined
// and documented (SDK-4013). This will cause quite a bit of cleanup work in 
// multiple repos, so I only want to do it once we know what we need.

#include <logging.h>
#include <testutils.h>

static inline uintptr_t get_core_base_address(void) { return 0x10000000; }


#define N_AICORES (4)

#endif  // __SDK_ADAPTER_H__
