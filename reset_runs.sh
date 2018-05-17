echo "delete from run;" > tmp_delete_sql;
sqlite3 $1 < tmp_delete_sql;
rm tmp_delete_sql;
