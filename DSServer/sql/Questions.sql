-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Questions" cascade;
create table "Questions" (
	chapterId int,
	questionId int,
	bookRef varchar(10) null,
	otherInfo text null,
        primary key (chapterId, questionId)
);
alter table "Questions" owner to elixir;

