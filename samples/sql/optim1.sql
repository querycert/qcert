select name from (select * from faculty union select * from students) as staff where age = 30;
