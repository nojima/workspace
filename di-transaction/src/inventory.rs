use mysql;
use mysql::params;
use mysql::prelude::*;

pub trait Inventory {
    fn add_items(&mut self, tx: &mut mysql::Transaction, amount: i64) -> crate::Result<()>;
}

pub struct MySqlInventory {}

impl Inventory for MySqlInventory {
    // アイテムを指定された量だけ追加する
    fn add_items(&mut self, tx: &mut mysql::Transaction, amount: i64) -> crate::Result<()> {
        let user_id: i64 = 1;
        let item_id: i64 = 1;
        let stmt = "\
            UPDATE `inventory` \
               SET `amount` = `amount` + :amount \
             WHERE `user_id` = :user_id AND `item_id` = :item_id \
        ";
        tx.exec_drop(stmt, params!{
            "amount" => amount,
            "user_id" => user_id,
            "item_id" => item_id,
        })?;
        Ok(())
    }
}
