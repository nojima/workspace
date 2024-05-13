CREATE TABLE `users` (
    `user_id` bigint unsigned NOT NULL,
    `name` varchar(63) CHARSET ascii COLLATE ascii_general_ci NOT NULL,
    `display_name` varchar(63) NOT NULL,
    `password_hash` varchar(255) CHARSET ascii COLLATE ascii_bin NOT NULL,
    `created_at` datetime(6) NOT NULL,
    `deleted_at` datetime(6) NOT NULL DEFAULT '9999-12-31 23:59:59.999999',
    PRIMARY KEY (`user_id`),
    UNIQUE KEY `name` (`name`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_bin ROW_FORMAT=DYNAMIC;
