package memory_preloading_pkg;

  // File existence checker
  function automatic bit file_exists(string file_path);
    int fd = $fopen(file_path, "r");
    bit success = (fd != 0);
    if (fd) $fclose(fd);
    return success;
  endfunction

endpackage
