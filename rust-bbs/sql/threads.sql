CREATE TABLE `threads` (
    `thread_id` bigint unsigned NOT NULL,
    `title` varchar(191) NOT NULL,
    `creator_id` bigint unsigned NOT NULL,
    `created_at` datetime(6) NOT NULL,
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_bin ROW_FORMAT=DYNAMIC;
