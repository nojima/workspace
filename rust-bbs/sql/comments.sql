CREATE TABLE `comments` (
    `thread_id` bigint unsigned NOT NULL,
    `comment_id` bigint unsigned NOT NULL,
    `user_id` bigint unsigned NOT NULL,
    `created_at` datetime(6) NOT NULL,
    `body` text NOT NULL,
    PRIMARY KEY (`thread_id`, `comment_id`),
    CONSTRAINT `fk_comments_to_users_on_id`
        FOREIGN KEY (`user_id`) REFERENCES `users` (`id`),
    CONSTRAINT `fk_comments_to_threads_on_id`
        FOREIGN KEY (`thread_id`) REFERENCES `threads` (`id`) ON DELETE CASCADE,
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_bin ROW_FORMAT=DYNAMIC;
