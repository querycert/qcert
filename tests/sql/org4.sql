select count(*) from (select * from employees union all select * from students) as persons where age = 32;
