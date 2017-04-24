select name from (select * from persons union select * from persons) as staff where age = 30;
