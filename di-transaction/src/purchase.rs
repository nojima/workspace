use crate::inventory::*;
use crate::wallet::*;

use mysql;
use anyhow::anyhow;

// アイテムを購入する
pub fn purchase_item(
    inventory: &mut Inventory,
    wallet: &mut Wallet,
    conn: &mut mysql::PooledConn
) -> crate::Result<()> {

    let mut tx = conn.start_transaction(mysql::TxOpts::default())?;

    // 残高が十分か確認する
    let current_balance = wallet.get_balance(&mut tx)?;
    if current_balance < 100 {
        return Err(anyhow!("balance is not sufficient: current_balance={}", current_balance));
    }

    // アイテムを追加し、残高を減らす
    inventory.add_items(&mut tx, 1)?;
    wallet.pay(&mut tx, 100)?;

    tx.commit()?;
    Ok(())
}
