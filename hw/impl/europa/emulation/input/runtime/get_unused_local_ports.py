#!/usr/bin/env python3

import socket
import argparse


def get_unused_local_ports(n):
    socket_list = []

    for _ in range(args.n):
        socket_list.append(socket.socket(socket.AF_INET, socket.SOCK_STREAM))
        socket_list[-1].bind(('', 0))

    port_list = [addr[1] for addr in [s.getsockname() for s in socket_list]]

    for s in socket_list:
        s.close()

    return port_list


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="print available local ports")
    parser.add_argument('n', type=int, nargs='?', default=1,
                        help='number of ports to be returned')
    args = parser.parse_args()

    port_list = get_unused_local_ports(args.n)
    print(" ".join([str(port) for port in port_list]))
