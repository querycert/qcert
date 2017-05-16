select name from (select * from employees union select * from students) as persons where age = 32;
