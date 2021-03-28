mod inventory;
mod wallet;
mod purchase;

use inventory::*;
use wallet::*;
use purchase::*;

use mysql;

type Result<T> = anyhow::Result<T>;

fn main() -> Result<()> {
    let url = "mysql://root:root@localhost:3306/di_transaction";
    let pool = mysql::Pool::new(url)?;
    let mut conn = pool.get_conn()?;

    let mut inventory = MySqlInventory{};
    let mut wallet = MySqlWallet{};

    purchase_item(&mut inventory, &mut wallet, &mut conn)?;

    Ok(())
}
