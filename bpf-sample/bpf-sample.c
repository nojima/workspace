#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <arpa/inet.h>
#include <linux/filter.h>
#include <linux/if_ether.h>
#include <net/if.h>
#include <netpacket/packet.h>
#include <sys/ioctl.h>
#include <sys/socket.h>

void print_mac_address(unsigned char* addr) {
    for (int i = 0; i < ETH_ALEN; i++) {
        if (i != 0)
            putc(':', stdout);
        printf("%02x", addr[i]);
    }
}

const char* proto_to_string(int proto) {
    switch (proto) {
    case ETH_P_IP: return "IP";
    case ETH_P_ARP: return "ARP";
    case ETH_P_LOOP: return "LOOP";
    default: return "???";
    }
}

int main(int argc, char** argv) {
    if (argc <= 1) {
        fprintf(stderr, "Usage: ./bpf-sample INTERFACE\n");
        exit(2);
    }
    char* if_name = argv[1];
    if (strlen(if_name) > IFNAMSIZ) {
        fprintf(stderr, "Too long interface naem: %s\n", if_name);
        exit(2);
    }

    int sock = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
    if (sock == -1) {
        perror("Failed to create a socket");
        exit(1);
    }

    struct ifreq ifr;
    memset(&ifr, 0, sizeof(ifr));
    strncpy(ifr.ifr_name, if_name, IFNAMSIZ);

    if (ioctl(sock, SIOCGIFINDEX, &ifr) == -1) {
        perror("Failed to get interface index");
        exit(1);
    }

    struct sockaddr_ll saddr;
    memset(&saddr, 0, sizeof(saddr));
    saddr.sll_family = AF_PACKET;
    saddr.sll_protocol = htons(ETH_P_ALL);
    saddr.sll_ifindex = ifr.ifr_ifindex;

    if (bind(sock, (struct sockaddr*)&saddr, sizeof(saddr)) == -1) {
        perror("Failed to bind");
        exit(1);
    }

    printf("%-17s  %-17s  %-4s  %7s\n", "DESTINATION", "SOURCE", "PROTO", "LENGTH");
    for (;;) {
        unsigned char buff[4096];
        ssize_t len = recv(sock, buff, sizeof(buff), 0);
        if (len == -1) {
            perror("Failed to recv");
            exit(1);
        }
        struct ethhdr* ethhdr = (struct ethhdr*)buff;
        int proto = ntohs(ethhdr->h_proto);
        print_mac_address(ethhdr->h_dest);
        printf("  ");
        print_mac_address(ethhdr->h_source);
        printf("  %-5s  %7zd\n", proto_to_string(proto), len);
    }

    return 0;
}
