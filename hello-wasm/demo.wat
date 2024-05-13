(module
    (import "wasi_snapshot_preview1" "fd_write"
        ;; fd_write(fd, *iovs, iovs_len, *nwritten) -> i32
        (func $fd_write (param i32 i32 i32 i32) (result i32))
    )
    (memory 1)
    (export "memory" (memory 0))

    (data (i32.const 8) "Hello, world!\n")

    (func $main (export "_start")
        ;; Create new io vector at the memory location 0
        (i32.store (i32.const 0) (i32.const 8))  ;; iov.iov_base
        (i32.store (i32.const 4) (i32.const 14)) ;; iov.iov_len -- length of "Hello, world!\n"

        (call $fd_write
            (i32.const 1)  ;; fd (1 for stdout)
            (i32.const 0)  ;; *iovs
            (i32.const 1)  ;; iovs_len
            (i32.const 20) ;; nwritten
        )
        drop
    )
)
