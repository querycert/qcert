select name from (select * from persons union all select * from persons) as staff where age = 30;
