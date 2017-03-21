-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Result";
create table "Result" (
    id serial primary key,
    plan_id int not null references "Plan"(id) on update cascade on delete cascade,
    name varchar(50) not null,
    rid varchar(10),
    text varchar(200),
    value varchar(1000),
    constraint uniq_result unique (plan_id, name)
);
alter table "Result" owner to elixir;

