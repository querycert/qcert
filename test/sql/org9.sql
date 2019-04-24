select *
from employees
except
select *
from employees
where age = 32
;
