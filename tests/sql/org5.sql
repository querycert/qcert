SELECT *
FROM (SELECT name,age FROM employees
       UNION ALL
      SELECT name,age FROM students) AS persons
WHERE age = 32;
