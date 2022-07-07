# cod2packetparser
Call of Duty 2 UDP Proxy with packet translation between 1.0/1.2/1.3 versions.

Currently WIP, lots missing.

Compile: g++ -m32 -L/lib32 -static -Wno-write-strings -D COD_VERSION=COD2_1_0 main.cpp -o proxy_server
Usage: ./proxy_server \<Your IP\> -Dest Port- -Your IP- -Source Port- eg. ./proxy_server 172.30.132.237 28965 172.30.132.237 28960
