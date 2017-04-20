select name from (select * from faculty union all select * from students) as staff where age = 30;
