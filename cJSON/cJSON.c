/*
  Copyright (c) 2009 Dave Gamble

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
  THE SOFTWARE.
*/

/* cJSON */
/* JSON parser in C. */

#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <float.h>
#include <limits.h>
#include <ctype.h>
#include "cJSON.h"

static const char *ep; //error pointer用于标记JSON字符串的出错位置

const char *cJSON_GetErrorPtr(void)
{
    return ep;
}

static int cJSON_strcasecmp(const char *s1,const char *s2)
{
    if (!s1) return (s1==s2)?0:1;
    if (!s2) return 1;
    for(; tolower(*s1) == tolower(*s2); ++s1, ++s2)	if(*s1 == 0)	return 0;
    return tolower(*(const unsigned char *)s1) - tolower(*(const unsigned char *)s2);
}

static void *(*cJSON_malloc)(size_t sz) = malloc;
static void (*cJSON_free)(void *ptr) = free;

//字符串复制,返回副本的指针
static char* cJSON_strdup(const char* str)
{
    size_t len;
    char* copy;

    len = strlen(str) + 1;
    if (!(copy = (char*)cJSON_malloc(len))) return 0;
    memcpy(copy,str,len);
    return copy;
}

void cJSON_InitHooks(cJSON_Hooks* hooks)
{
    if (!hooks) { /* Reset hooks */
        cJSON_malloc = malloc;
        cJSON_free = free;
        return;
    }

    cJSON_malloc = (hooks->malloc_fn)?hooks->malloc_fn:malloc;
    cJSON_free	 = (hooks->free_fn)?hooks->free_fn:free;
}

/* 为cJSON结构分配空间并初始化为０. */
static cJSON *cJSON_New_Item(void)
{
    cJSON* node = (cJSON*)cJSON_malloc(sizeof(cJSON));
    if (node) memset(node,0,sizeof(cJSON));
    return node;
}

/*递归的释放cJSON的内存空间
  将JSON文本进行解析所生成的cJSON结构的空间是malloc的方式分配的，如果用完不及时释放会造成内存泄露 
  由于cJSON对象是树型嵌套结构,对它的释放通过该函数实现. */
void cJSON_Delete(cJSON *c)
{
    cJSON *next;
    while (c) {
        next=c->next;
        if (!(c->type&cJSON_IsReference) && c->child) cJSON_Delete(c->child);//递归的进行释放
        if (!(c->type&cJSON_IsReference) && c->valuestring) cJSON_free(c->valuestring);
        if (!(c->type&cJSON_StringIsConst) && c->string) cJSON_free(c->string);
        cJSON_free(c);
        c=next;
    }
}

/* 解析输入文本生成一个数字,并填充结果项. 
　 参数:item:要填充的cJSON
        num:　要解析成数据的字符串(如 buf[]="12.345E6xyz") 
   返回值: 指向不符合数字的那个字符 (对上面的buf而言,返回指向x的指针)
   使用的计算方法: 12.345E6 --> 12345E(-3+6)--> 12345*(10^(-3+6)) */
static const char *parse_number(cJSON *item,const char *num)
{
    double n=0,sign=1,scale=0;
    int subscale=0,signsubscale=1;

    if (*num=='-') sign=-1,num++;	/* 判断是否为负数 */
    if (*num=='0') num++;			/* is zero */
    if (*num>='1' && *num<='9')	
		do	
			n=(n*10.0)+(*num++ -'0');
        while (*num>='0' && *num<='9');	/* Number? */
		
    if (*num=='.' && num[1]>='0' && num[1]<='9') {
        num++;		   /* Fractional part? */
        do	
			n=(n*10.0)+(*num++ -'0'),scale--;
        while (*num>='0' && *num<='9');
    }
    if (*num=='e' || *num=='E') {	/* Exponent? */
        num++;
        if (*num=='+') num++;
        else if (*num=='-') signsubscale=-1,num++;		/* With sign? */
        while (*num>='0' && *num<='9') subscale=(subscale*10)+(*num++ - '0');	/* Number? */
    }

    n=sign*n*pow(10.0,(scale+subscale*signsubscale));	/* number = +/- number.fraction * 10^+/- exponent */

    item->valuedouble=n;
    item->valueint=(int)n;
    item->type=cJSON_Number;
    return num;
}

//返回大于等于x的最小的2的N次方数
static int pow2gt (int x)
{
    --x;	//先减1, 使得对x本就是2的N次方的情况的处理统一起来
	//使x的二进制中最高位的1不断向低位扩展,最终使得最高位为1的右边的所有位均被置1
	//如:0001 xxxx xxxx xxxx(x表示0或１)->0001 1xxx xxxx xxxx ->0001 111x xxxx xxxx -> 0001 1111 111x xxxx ->...
    x|=x>>1; //将最位的1向低位扩展一次,使得高位出现两个连续的1
    x|=x>>2; //使高位两个连续的1变成4个连续的1。...最后使得最高位为1的右边的所有位均为1
    x|=x>>4;
    x|=x>>8;
    x|=x>>16;
    return x+1;
}

//存储结构,用于存放　将结构化的cJSON转换为文本格式的JSON描述　的内容
typedef struct {
    char *buffer; //存放文本格式的JSON描述
    int length; //buffer空间的大小
    int offset; //已使用的buffer的大小
} printbuffer;

/* 判断存储结构p的缓冲区中是否具有needed个剩余空间,没有则重新分配足够的空间
   参数:p:存储结构指针
        needed: 需要的空间大小　
   返回:指向空闲空间起始位置的指针,失败-返回0
   */
static char* ensure(printbuffer *p,int needed)
{
    char *newbuffer;
    int newsize;
    if (!p || !p->buffer) return 0;
    needed+=p->offset;
    if (needed<=p->length)//原p->buffer中还有needed个可用空间
		return p->buffer+p->offset;

	//如果原p->buffer中没有needed个可用空间,则需要重新分配
    newsize=pow2gt(needed);//得到大于等于needed的最小的2的N次方数,用于分配空间－使分配的空间大小为2^N
    newbuffer=(char*)cJSON_malloc(newsize);//分配空间
    if (!newbuffer) {
        cJSON_free(p->buffer);
        p->length=0,p->buffer=0;
        return 0;
    }
    if (newbuffer) memcpy(newbuffer,p->buffer,p->length);
    cJSON_free(p->buffer);
    p->length=newsize;
    p->buffer=newbuffer;
    return newbuffer+p->offset;
}

//获取p的当前使用buffer的大小(用于更新offset)
static int update(printbuffer *p)
{
    char *str;
    if (!p || !p->buffer) return 0;
    str=p->buffer+p->offset;
    return p->offset+strlen(str);
}

/*  将对应类型为Number的结构化的cJSON转换为文本格式的JSON描述,并存储到适当位置. 
　　参数:item:要转换为JSON文本格式的cJSON对象指针
         P:将转换后的内容写入p的适当位置，为NULL时在内部分配空间
    返回:存放转换结果的首地址*/
static char *print_number(cJSON *item,printbuffer *p)
{
    char *str=0;
    double d=item->valuedouble;
    if (d==0) {
        if (p)	str=ensure(p,2);
        else	str=(char*)cJSON_malloc(2);	/* special case for 0. */
        if (str) strcpy(str,"0");
    } 
	else 
		//EPSILON是double的最小误差。 是EPSILON+X不等于X的最小的正数
		//下面这个判断的作用是:是否将JSON的Number类型判定为int
	if (fabs(((double)item->valueint)-d)<=DBL_EPSILON && d<=INT_MAX && d>=INT_MIN) {//将Number当作int处理
        if (p)	str=ensure(p,21);
        else	str=(char*)cJSON_malloc(21);	/* 2^64+1 的大小能用 20个字符表示,再加一个'\0'结束符. */
        if (str)	sprintf(str,"%d",item->valueint);
    } else {//将Number当作double处理
        if (p)	str=ensure(p,64);
        else	str=(char*)cJSON_malloc(64);	/* This is a nice tradeoff. */
        if (str) {
            if (fabs(floor(d)-d)<=DBL_EPSILON && fabs(d)<1.0e60)sprintf(str,"%.0f",d);
            else if (fabs(d)<1.0e-6 || fabs(d)>1.0e9)			sprintf(str,"%e",d);
            else												sprintf(str,"%f",d);
        }
    }
    return str;
}

static unsigned parse_hex4(const char *str)
{
    unsigned h=0;
    if (*str>='0' && *str<='9') h+=(*str)-'0';
    else if (*str>='A' && *str<='F') h+=10+(*str)-'A';
    else if (*str>='a' && *str<='f') h+=10+(*str)-'a';
    else return 0;
    h=h<<4;
    str++;
    if (*str>='0' && *str<='9') h+=(*str)-'0';
    else if (*str>='A' && *str<='F') h+=10+(*str)-'A';
    else if (*str>='a' && *str<='f') h+=10+(*str)-'a';
    else return 0;
    h=h<<4;
    str++;
    if (*str>='0' && *str<='9') h+=(*str)-'0';
    else if (*str>='A' && *str<='F') h+=10+(*str)-'A';
    else if (*str>='a' && *str<='f') h+=10+(*str)-'a';
    else return 0;
    h=h<<4;
    str++;
    if (*str>='0' && *str<='9') h+=(*str)-'0';
    else if (*str>='A' && *str<='F') h+=10+(*str)-'A';
    else if (*str>='a' && *str<='f') h+=10+(*str)-'a';
    else return 0;
    return h;
}

/* 将输入文本解析成字符串,并填充item。
   参数:item:要填充的cJSON
        str :要解析的字符串
   返回:解析生成的字符串. */
static const unsigned char firstByteMark[7] = { 0x00, 0x00, 0xC0, 0xE0, 0xF0, 0xF8, 0xFC };
static const char *parse_string(cJSON *item,const char *str)
{
    const char *ptr=str+1;//使ptr指向第一个字符,跳过表示字符串的"号
    char *ptr2;
    char *out;
    int len=0;
    unsigned uc,uc2;
    if (*str!='\"') {//检查str是否为JSON的string类型
        ep=str;    /* not a string! */
        return 0;
    }

    while (*ptr!='\"' && *ptr && ++len) if (*ptr++ == '\\') ptr++;	/* Skip escaped quotes. */

    out=(char*)cJSON_malloc(len+1);	/* This is how long we need for the string, roughly. */
    if (!out) return 0;

    ptr=str+1;
    ptr2=out;
    while (*ptr!='\"' && *ptr) {
        if (*ptr!='\\') *ptr2++=*ptr++;
        else {//JSON文本中包含有转义字符
            ptr++;
            switch (*ptr) {
                case 'b':
                    *ptr2++='\b';break;
                case 'f':
                    *ptr2++='\f';break;
                case 'n':
                    *ptr2++='\n';break;
                case 'r':
                    *ptr2++='\r'; break;
                case 't':
                    *ptr2++='\t';break;
                case 'u':	 /* utf16转码为utf8.　这部分实现参考unicode编码 */
                    uc=parse_hex4(ptr+1);
                    ptr+=4;	/* get the unicode char. */

                    if ((uc>=0xDC00 && uc<=0xDFFF) || uc==0)	break;	/* check for invalid.	*/

                    if (uc>=0xD800 && uc<=0xDBFF) {	/* UTF16 surrogate pairs.	*/
                        if (ptr[1]!='\\' || ptr[2]!='u')	break;	/* missing second-half of surrogate.	*/
                        uc2=parse_hex4(ptr+3);
                        ptr+=6;
                        if (uc2<0xDC00 || uc2>0xDFFF)		break;	/* invalid second-half of surrogate.	*/
                        uc=0x10000 + (((uc&0x3FF)<<10) | (uc2&0x3FF));
                    }

                    len=4;
                    if (uc<0x80) len=1;
                    else if (uc<0x800) len=2;
                    else if (uc<0x10000) len=3;
                    ptr2+=len;

                    switch (len) {
                        case 4:
                            *--ptr2 =((uc | 0x80) & 0xBF);uc >>= 6;
                        case 3:
                            *--ptr2 =((uc | 0x80) & 0xBF);uc >>= 6;
                        case 2:
                            *--ptr2 =((uc | 0x80) & 0xBF); uc >>= 6;
                        case 1:
                            *--ptr2 =(uc | firstByteMark[len]);
                    }
                    ptr2+=len;break;
                default:
                    *ptr2++=*ptr;break;
            }
            ptr++;
        }
    }
    *ptr2=0;
    if (*ptr=='\"') ptr++;
    item->valuestring=out;
    item->type=cJSON_String;
    return ptr;
}

/* Render the cstring provided to an escaped version that can be printed. */
/*  将字符串str存储到p的空闲位置. 
　　参数:str:要存储的字符串
         P:将转换后的内容写入p的适当位置，为NULL时在内部分配空间
    返回:存放转换结果的首地址,失败－返回0*/
static char *print_string_ptr(const char *str,printbuffer *p)
{
    const char *ptr;
    char *ptr2,*out;
    int len=0,flag=0;
    unsigned char token;

	//检查JSON的String类型中是否包含特殊字符
    for (ptr=str; *ptr; ptr++) 
		flag|=((*ptr>0 && *ptr<32)||(*ptr=='\"')||(*ptr=='\\'))?1:0;
	
    if (!flag) {
        len=ptr-str;
        if (p) out=ensure(p,len+3);
        else out=(char*)cJSON_malloc(len+3);
        if (!out) return 0;
        ptr2=out;
        *ptr2++='\"';
        strcpy(ptr2,str);
        ptr2[len]='\"';
        ptr2[len+1]=0;
        return out;
    }

    if (!str) {
        if (p)	out=ensure(p,3);
        else	out=(char*)cJSON_malloc(3);
        if (!out) return 0;
        strcpy(out,"\"\"");
        return out;
    }

	//包含特殊字符时的处理
    ptr=str;
    while ((token=*ptr) && ++len) {
        if (strchr("\"\\\b\f\n\r\t",token)) len++;//为转义字符要多占一个字符, 如:ASCII:08对应转义字符\b
        else if (token<32) len+=5;//对满足这种条件的字符码在JSON中以\uxxxx形式存储 
        ptr++;
    }

    if (p)	out=ensure(p,len+3);
    else	out=(char*)cJSON_malloc(len+3);
    if (!out) return 0;

    ptr2=out;
    ptr=str;
    *ptr2++='\"';
    while (*ptr) {
        if ((unsigned char)*ptr>31 && *ptr!='\"' && *ptr!='\\') *ptr2++=*ptr++;//正常字符直接复制
        else {
            *ptr2++='\\';//转义字符前加'\'
            switch (token=*ptr++) {
                case '\\':
                    *ptr2++='\\';
                    break;
                case '\"':
                    *ptr2++='\"';
                    break;
                case '\b':
                    *ptr2++='b';
                    break;
                case '\f':
                    *ptr2++='f';
                    break;
                case '\n':
                    *ptr2++='n';
                    break;
                case '\r':
                    *ptr2++='r';
                    break;
                case '\t':
                    *ptr2++='t';
                    break;
                default:
                    sprintf(ptr2,"u%04x",token);
                    ptr2+=5;
                    break;	/* escape and print */
            }
        }
    }
    *ptr2++='\"';
    *ptr2++=0;
    return out;
}
/* Invote print_string_ptr (which is useful) on an item. */
static char *print_string(cJSON *item,printbuffer *p)
{
    return print_string_ptr(item->valuestring,p);
}

/* Predeclare these prototypes. */
static const char *parse_value(cJSON *item,const char *value);
static char *print_value(cJSON *item,int depth,int fmt,printbuffer *p);
static const char *parse_array(cJSON *item,const char *value);
static char *print_array(cJSON *item,int depth,int fmt,printbuffer *p);
static const char *parse_object(cJSON *item,const char *value);
static char *print_object(cJSON *item,int depth,int fmt,printbuffer *p);




/* 工具:函数跳过不可打印字符 */
static const char *skip(const char *in)
{
    while (in && *in && (unsigned char)*in<=32) in++;
    return in;
}

/* 解析对象,创建一个新的根并填充.
　参数:value:要序列化为CJSON的字符串
　　　 return_parse_end:[out]用于输出解析完成该cJSON时,JSON字符串的结束位置(指针),为NULL表示不返回
       require_null_terminated:JSON字符串是否需要以'\0'结束
  返回值:成功:返回一个cJSON指针
  　　　 失败:返回NULL,出错位置可由cJSON_GetErrorPtr()获取
  注意:使用该函数会通过malloc函数在内存中开辟一个空间，使用完成需要手动释放(通过cJSON_Delete)。
 */
cJSON *cJSON_ParseWithOpts(const char *value,const char **return_parse_end,int require_null_terminated)
{
    const char *end=0;
    cJSON *c=cJSON_New_Item();
    ep=0;
    if (!c) return 0;       /* memory fail */

    end=parse_value(c,skip(value));//解析器的核心
    if (!end)	{
        cJSON_Delete(c);    /* 解析失败时。ep指针将被设置. */
        return 0;
    }

    /*当JSON需要以null结尾时。进行检查*/
    /* if we require null-terminated JSON without appended garbage, skip and then check for a null terminator */
    if (require_null_terminated) {
        end=skip(end);
        if (*end) {
            cJSON_Delete(c);
            ep=end;
            return 0;
        }
    }
    if (return_parse_end) *return_parse_end=end;
    return c;
}






/*解析JSON数据包,按照cJSON结构体的结构序列化传入的数据包
　参数:value:要序列化为CJSON的数据
  返回值:成功:返回一个cJSON指针
  　　　 失败:返回NULL,出错位置可由cJSON_GetErrorPtr()获取
  注意:使用该函数会通过malloc函数在内存中开辟一个空间，使用完成需要手动释放(通过cJSON_Delete)。
 */
cJSON *cJSON_Parse(const char *value)
{
    return cJSON_ParseWithOpts(value,0,0);
}




/* Render a cJSON item/entity/structure to text. */
/*将传入的cJSON转换成一个可打印的cJSON字符串
  参数:item: 结构化的cJSON对象
  返回: 文本化的cJSON
　注意:这个函数在内部分配空间,所以使用完后要用free()释放*/
char *cJSON_Print(cJSON *item)
{
    return print_value(item,0,1,0);
}
char *cJSON_PrintUnformatted(cJSON *item)
{
    return print_value(item,0,0,0);
}




char *cJSON_PrintBuffered(cJSON *item,int prebuffer,int fmt)
{
    printbuffer p;
    p.buffer=(char*)cJSON_malloc(prebuffer);
    p.length=prebuffer;
    p.offset=0;
    return print_value(item,0,fmt,&p);
    return p.buffer;
}




/* 解析器的核心——当遇到文本,用适当的过程处理.  --有的分支使用了间接递归来处理 */
static const char *parse_value(cJSON *item,const char *value)
{
    if (!value)						return 0;	/* Fail on null. */
    if (!strncmp(value,"null",4))	{
        item->type=cJSON_NULL;
        return value+4;
    }
    if (!strncmp(value,"false",5))	{
        item->type=cJSON_False;
        return value+5;
    }
    if (!strncmp(value,"true",4))	{
        item->type=cJSON_True;
        item->valueint=1;
        return value+4;
    }
    if (*value=='\"')				{
        return parse_string(item,value);
    }
    if (*value=='-' || (*value>='0' && *value<='9'))	{
        return parse_number(item,value);
    }
    if (*value=='[')				{
        return parse_array(item,value);
    }
    if (*value=='{')				{
        return parse_object(item,value);
    }

    ep=value;
    return 0;	/* 失败. */
}



/* 将结构化的cJSON转换成为文本格式的JSON。(格式化输出和非格式化输出)
   参数:　item:要转换的cJSON(实际上是要转换的cJSON树的根节点)
          depth: 在指定格式化输出时在左侧填充的空格数 
          fmt: 是否设置输出的格式(缩进),非0表示有格式的输出,0无格式的输出
          p: JSON的文本格式描述的存储位置,为NULL时空间在内部分配
   返回值:存放转换结果的首地址,失败－返回0*/
static char *print_value(cJSON *item,int depth,int fmt,printbuffer *p)
{
    char *out=0;
    if (!item) return 0;
    if (p) {
        switch ((item->type)&255) {
            case cJSON_NULL:	{
                out=ensure(p,5);
                if (out) strcpy(out,"null");
                break;
            }
            case cJSON_False:	{
                out=ensure(p,6);
                if (out) strcpy(out,"false");
                break;
            }
            case cJSON_True:	{
                out=ensure(p,5);
                if (out) strcpy(out,"true");
                break;
            }
            case cJSON_Number:
                out=print_number(item,p);
                break;
            case cJSON_String:
                out=print_string(item,p);
                break;
            case cJSON_Array:
                out=print_array(item,depth,fmt,p);
                break;
            case cJSON_Object:
                out=print_object(item,depth,fmt,p);
                break;
        }
    } else {
        switch ((item->type)&255) {
            case cJSON_NULL:
                out=cJSON_strdup("null");
                break;
            case cJSON_False:
                out=cJSON_strdup("false");
                break;
            case cJSON_True:
                out=cJSON_strdup("true");
                break;
            case cJSON_Number:
                out=print_number(item,0);
                break;
            case cJSON_String:
                out=print_string(item,0);
                break;
            case cJSON_Array:
                out=print_array(item,depth,fmt,0);
                break;
            case cJSON_Object:
                out=print_object(item,depth,fmt,0);
                break;
        }
    }
    return out;
}


/* 解析json,根据输入文本构建一个JSON数组. 
   参数: item:要构建的cJSON
         value:用于构建JSON数组的json格式的字符串
   返回:　解析完成后,下一个要解析的位置.失败返回0*/
static const char *parse_array(cJSON *item,const char *value)
{
    cJSON *child;
    if (*value!='['){//检查是否为JSON数组类型
        ep=value;    /* not an array! */
        return 0;
    }

    item->type=cJSON_Array;
    value=skip(value+1);
    if (*value==']') return value+1;	/* 空数组. */

    item->child=child=cJSON_New_Item();//为JSON数组的元素分配空间(将JSON数组与其元素的关系看作父子关系)
    if (!item->child) return 0;		 
    value=skip(parse_value(child,skip(value)));	/* JSON的数组是嵌套类型(数组的元素可以是任意JSON类型),使用间接递归来处理之 */
    if (!value) return 0;

    while (*value==',') {//当cJSON数组有下一个元素,处理下一个元素
        cJSON *new_item;
        if (!(new_item=cJSON_New_Item())) return 0; 	/* memory fail */
        child->next=new_item;
        new_item->prev=child;
		
        child=new_item;
        value=skip(parse_value(child,skip(value+1)));
        if (!value) return 0;	/* memory fail */
    }

    if (*value==']') return value+1;	/* JSON数组解析结束 */
    ep=value;
    return 0;	/* 解析失败,提供用于解析的文本有缺陷. */
}

/*  将类型为array的结构化的cJSON转换为文本格式的JSON描述,并存储到适当位置. 
　　参数:item:要转换为JSON文本格式的cJSON对象指针
         depth: 在指定格式化输出时在左侧填充的空格数 
         fmt: 是否设置输出的格式(缩进),非0表示有格式的输出,0无格式的输出
         P:将转换后的内容写入p的适当位置，为NULL时在内部分配空间
    返回:存放转换结果的首地址*/
    
static char *print_array(cJSON *item,int depth,int fmt,printbuffer *p)
{
    char **entries;
    char *out=0,*ptr,*ret;
    int len=5;
    cJSON *child=item->child;
    int numentries=0,i=0,fail=0;
    size_t tmplen=0;

    /* 计算cJSON的数组类型对象有多少个元素(孩子) */
    while (child) numentries++,child=child->next;
    /* 当cJSON的数组类型对象没有孩子时 */
    if (!numentries) {
        if (p)	out=ensure(p,3);
        else	out=(char*)cJSON_malloc(3);
        if (out) strcpy(out,"[]");
        return out;
    }

	/* 有孩子 */
	//指定转换结果的存储位置
    if (p) {
        /* 构成输出的JSON数组类型. */
        i=p->offset;
        ptr=ensure(p,1);
        if (!ptr) return 0;
        *ptr='[';
        p->offset++;
        child=item->child;
        while (child && !fail) {
            print_value(child,depth+1,fmt,p);//递归的处理JSON元素
            p->offset=update(p);
			//当指定以格式化方式转换时JSON数组元素之间的逗号分隔符后面加一个空格 [x, y],不格式化时[x,y]
            if (child->next) {
                len=fmt?2:1; 
                ptr=ensure(p,len+1);
                if (!ptr) return 0;
                *ptr++=',';
                if(fmt)*ptr++=' ';
                *ptr=0;
                p->offset+=len;
            }
            child=child->next;
        }
        ptr=ensure(p,2);
        if (!ptr) return 0;
        *ptr++=']';
        *ptr=0;
        out=(p->buffer)+i;
    } else {//没有指定转换结果的存储位置时,需要内部分配

		/* 分配一个空间存放指向JSON数组元素转换结果的地址(其元素的空间在print_value()中分配)
		  通过它将JSON数组元素转换结果复制到一个连续的空间中*/
        entries=(char**)cJSON_malloc(numentries*sizeof(char*));
        if (!entries) return 0;
        memset(entries,0,numentries*sizeof(char*));
        /* Retrieve all the results: */
        child=item->child;
        while (child && !fail) {
            ret=print_value(child,depth+1,fmt,0);
            entries[i++]=ret;
            if (ret) len+=strlen(ret)+2+(fmt?1:0);
            else fail=1;//失败
            child=child->next;
        }

        /* If we didn't fail, try to malloc the output string */
        if (!fail)	out=(char*)cJSON_malloc(len);
        /* If that fails, we fail. */
        if (!out) fail=1;

        /* Handle failure. */
        if (fail) {
            for (i=0; i<numentries; i++) if (entries[i]) cJSON_free(entries[i]);
            cJSON_free(entries);
            return 0;
        }

        /* Compose the output array. */
        *out='[';
        ptr=out+1;
        *ptr=0;
        for (i=0; i<numentries; i++) {
            tmplen=strlen(entries[i]);
            memcpy(ptr,entries[i],tmplen);
            ptr+=tmplen;
            if (i!=numentries-1) {
                *ptr++=',';
                if(fmt)*ptr++=' ';
                *ptr=0;
            }
            cJSON_free(entries[i]);
        }
        cJSON_free(entries);
        *ptr++=']';
        *ptr++=0;
    }
    return out;
}

/* 解析json,用提供的字符串构建一个JSON对象
   参数: item:要构建的cJSON
         value:用于构建的json格式的字符串
   返回:　解析完成后,下一个要解析的位置.失败返回0*/
static const char *parse_object(cJSON *item,const char *value)
{
    cJSON *child;
    if (*value!='{')	{//检查要解析的是否为json对象
        ep=value;    /* not an object! */
        return 0;
    }

    item->type=cJSON_Object;
    value=skip(value+1);
    if (*value=='}') return value+1;	/* 空的对象. */

    item->child=child=cJSON_New_Item(); //为JSON对象的元素分配空间(将JSON对象与其元素的关系看作父子关系)
    if (!item->child) return 0;
	
	/*JSON对象的元素格式为 string:value 。其中string存到cJSON的string字段中，
	　而通过parse_string()解析出来的字符串是存储在cJSON的valuestring字段中,所以要进行下面几步*/
    value=skip(parse_string(child,skip(value)));
    if (!value) return 0;
    child->string=child->valuestring;
    child->valuestring=0;
    if (*value!=':') {
        ep=value;    /* fail! */
        return 0;
    }
    value=skip(parse_value(child,skip(value+1)));	/* JSON的对象的value部分是嵌套类型(value部分可以是任意JSON类型),使用间接递归来处理之 */
    if (!value) return 0;

    while (*value==',') {//当cJSON对象有下一个元素,处理下一个元素
        cJSON *new_item;
        if (!(new_item=cJSON_New_Item()))	return 0; /* memory fail */
        child->next=new_item;
        new_item->prev=child;
        child=new_item;
        value=skip(parse_string(child,skip(value+1)));/* 解析JSON的对象的string部分*/
        if (!value) return 0;
        child->string=child->valuestring;
        child->valuestring=0;
        if (*value!=':') {
            ep=value;    /* fail! */
            return 0;
        }
        value=skip(parse_value(child,skip(value+1)));	/* skip any spacing, get the value. */
        if (!value) return 0;
    }

    if (*value=='}') return value+1;	/* end of array */
    ep=value;
    return 0;	/* malformed. */
}

/*  将类型为object的结构化的cJSON转换为文本格式的JSON描述,并存储到适当位置. 
　　参数:item:要转换为JSON文本格式的cJSON对象指针
         depth: 在指定格式化输出时在左侧填充的空格数 
         fmt: 是否设置输出的格式(缩进),非0表示有格式的输出,0无格式的输出
         P:将转换后的内容写入p的适当位置，为NULL时在内部分配空间
    返回:存放转换结果的首地址*/
static char *print_object(cJSON *item,int depth,int fmt,printbuffer *p)
{
    char **entries=0,**names=0;
    char *out=0,*ptr,*ret,*str;
    int len=7,i=0,j;
    cJSON *child=item->child;
    int numentries=0,fail=0;
    size_t tmplen=0;
    /* 计算cJSON的object类型对象有多少个元素(孩子) */
    while (child) numentries++,child=child->next;
    /* 当cJSON的object类型对象没有孩子时 */
    if (!numentries) {
        if (p) out=ensure(p,fmt?depth+4:3);
        else	out=(char*)cJSON_malloc(fmt?depth+4:3);
        if (!out)	return 0;
        ptr=out;
        *ptr++='{';
        if (fmt) {
            *ptr++='\n';
            for (i=0; i<depth-1; i++) *ptr++='\t';
        }
        *ptr++='}';
        *ptr++=0;
        return out;
    }

	/* cJSON的object类型对象有元素时 */
    if (p) {
        /* Compose the output: */
        i=p->offset;
        len=fmt?2:1;
        ptr=ensure(p,len+1);
        if (!ptr) return 0;
        *ptr++='{';
        if (fmt) *ptr++='\n';
        *ptr=0;
        p->offset+=len;
        child=item->child;
        depth++;
        while (child) {
            if (fmt) {
                ptr=ensure(p,depth);
                if (!ptr) return 0;
                for (j=0; j<depth; j++) *ptr++='\t';
                p->offset+=depth;
            }
            print_string_ptr(child->string,p);
            p->offset=update(p);

            len=fmt?2:1;
            ptr=ensure(p,len);
            if (!ptr) return 0;
            *ptr++=':';
            if (fmt) *ptr++='\t';
            p->offset+=len;

            print_value(child,depth,fmt,p);
            p->offset=update(p);

            len=(fmt?1:0)+(child->next?1:0);
            ptr=ensure(p,len+1);
            if (!ptr) return 0;
            if (child->next) *ptr++=',';
            if (fmt) *ptr++='\n';
            *ptr=0;
            p->offset+=len;
            child=child->next;
        }
        ptr=ensure(p,fmt?(depth+1):2);
        if (!ptr) return 0;
        if (fmt)	for (i=0; i<depth-1; i++) *ptr++='\t';
        *ptr++='}';
        *ptr=0;
        out=(p->buffer)+i;
    } else {
        /* Allocate space for the names and the objects */
        entries=(char**)cJSON_malloc(numentries*sizeof(char*));
        if (!entries) return 0;
        names=(char**)cJSON_malloc(numentries*sizeof(char*));
        if (!names) {
            cJSON_free(entries);
            return 0;
        }
        memset(entries,0,sizeof(char*)*numentries);
        memset(names,0,sizeof(char*)*numentries);

        /* Collect all the results into our arrays: */
        child=item->child;
        depth++;
        if (fmt) len+=depth;
        while (child) {
            names[i]=str=print_string_ptr(child->string,0);
            entries[i++]=ret=print_value(child,depth,fmt,0);
            if (str && ret) len+=strlen(ret)+strlen(str)+2+(fmt?2+depth:0);
            else fail=1;
            child=child->next;
        }

        /* Try to allocate the output string */
        if (!fail)	out=(char*)cJSON_malloc(len);
        if (!out) fail=1;

        /* Handle failure */
        if (fail) {
            for (i=0; i<numentries; i++) {
                if (names[i]) cJSON_free(names[i]);
                if (entries[i]) cJSON_free(entries[i]);
            }
            cJSON_free(names);
            cJSON_free(entries);
            return 0;
        }

        /* Compose the output: */
        *out='{';
        ptr=out+1;
        if (fmt)*ptr++='\n';
        *ptr=0;
        for (i=0; i<numentries; i++) {
            if (fmt) for (j=0; j<depth; j++) *ptr++='\t';
            tmplen=strlen(names[i]);
            memcpy(ptr,names[i],tmplen);
            ptr+=tmplen;
            *ptr++=':';
            if (fmt) *ptr++='\t';
            strcpy(ptr,entries[i]);
            ptr+=strlen(entries[i]);
            if (i!=numentries-1) *ptr++=',';
            if (fmt) *ptr++='\n';
            *ptr=0;
            cJSON_free(names[i]);
            cJSON_free(entries[i]);
        }

        cJSON_free(names);
        cJSON_free(entries);
        if (fmt) for (i=0; i<depth-1; i++) *ptr++='\t';
        *ptr++='}';
        *ptr++=0;
    }
    return out;
}

/* Get Array size/item / object item. */
/*获取cJSON大小:返回数组或对象中的大小，只要该对象下包括其他对象，各对象一般以“,”分隔*/
int    cJSON_GetArraySize(cJSON *array)
{
    cJSON *c=array->child;
    int i=0;
    while(c)i++,c=c->next;
    return i;
}
/*以index的方式获取cJSON数组或对象相应的项
  返回数组或对象中相应index的项，找不到会返回NULL*/
cJSON *cJSON_GetArrayItem(cJSON *array,int item)
{
    cJSON *c=array->child;
    while (c && item>0) item--,c=c->next;
    return c;
}
/*以名称的方式获取cJSON数组或对象相应的项
  获取当前cJSON对象下有名字的cJSON对象，找不到会返回NULL*/
cJSON *cJSON_GetObjectItem(cJSON *object,const char *string)
{
    cJSON *c=object->child;
    while (c && cJSON_strcasecmp(c->string,string)) c=c->next;
    return c;
}


/* Utility for array list handling.  将prev与item组成链*/
static void suffix_object(cJSON *prev,cJSON *item)
{
    prev->next=item;
    item->prev=prev;
}
/* Utility for handling references. 创建一个引用,引用与被引用的对象共享资源,所以释放资源时要注意 */
static cJSON *create_reference(cJSON *item)
{
    cJSON *ref=cJSON_New_Item();
    if (!ref) return 0;
    memcpy(ref,item,sizeof(cJSON));
    ref->string=0;
    ref->type|=cJSON_IsReference;
    ref->next=ref->prev=0;
    return ref;
}

/* 在JSON的 array 中添加元素.－ 实际上向JSON的 Object 中添加元素也会调用这个函数
(在cJSON中对JSON的array与Object的区别仅是类型不同,且Object的string字段非NULL)*/
void   cJSON_AddItemToArray(cJSON *array, cJSON *item)
{
    cJSON *c=array->child;
    if (!item) return;
    if (!c) {////JSON的该array中没有元素
        array->child=item;
    } else {//JSON的该array中有元素(孩子)时,新加入的元素放到尾部
        while (c && c->next) c=c->next;
        suffix_object(c,item);
    }
}

/*在JOSN对象中添加一个元素, 因为是JSON对象的元素,所以其形式为key:value
  参数:object:在这个JSON对象中添加
  string: 对应添加元素的key
  item: 对应添加元素的value  */
void   cJSON_AddItemToObject(cJSON *object,const char *string,cJSON *item)
{
    if (!item) return;
    if (item->string) cJSON_free(item->string);
    item->string=cJSON_strdup(string);
    cJSON_AddItemToArray(object,item);
}

void   cJSON_AddItemToObjectCS(cJSON *object,const char *string,cJSON *item)
{
    if (!item) return;
    if (!(item->type&cJSON_StringIsConst) && item->string) cJSON_free(item->string);
    item->string=(char*)string;
    item->type|=cJSON_StringIsConst;
    cJSON_AddItemToArray(object,item);
}
void	cJSON_AddItemReferenceToArray(cJSON *array, cJSON *item)
{
    cJSON_AddItemToArray(array,create_reference(item));
}
void	cJSON_AddItemReferenceToObject(cJSON *object,const char *string,cJSON *item)
{
    cJSON_AddItemToObject(object,string,create_reference(item));
}

//从JSON的数组中分离出第which个元素(从0算起)
cJSON *cJSON_DetachItemFromArray(cJSON *array,int which)
{
    cJSON *c=array->child;
    while (c && which>0) c=c->next,which--;
    if (!c) return 0;
    if (c->prev) c->prev->next=c->next;
    if (c->next) c->next->prev=c->prev;
    if (c==array->child) array->child=c->next;
    c->prev=c->next=0;
    return c;
}
void   cJSON_DeleteItemFromArray(cJSON *array,int which)
{
    cJSON_Delete(cJSON_DetachItemFromArray(array,which));
}
//从JSON的对象中分离出名为string的元素
cJSON *cJSON_DetachItemFromObject(cJSON *object,const char *string)
{
    int i=0;
    cJSON *c=object->child;
    while (c && cJSON_strcasecmp(c->string,string)) i++,c=c->next;
    if (c) return cJSON_DetachItemFromArray(object,i);
    return 0;
}
void   cJSON_DeleteItemFromObject(cJSON *object,const char *string)
{
    cJSON_Delete(cJSON_DetachItemFromObject(object,string));
}

/* 在JSON的数组中的wihch位置插入一个新元素 */
void   cJSON_InsertItemInArray(cJSON *array,int which,cJSON *newitem)
{
    cJSON *c=array->child;
    while (c && which>0) c=c->next,which--;
    if (!c) {
        cJSON_AddItemToArray(array,newitem);
        return;
    }
    newitem->next=c;
    newitem->prev=c->prev;
    c->prev=newitem;
    if (c==array->child) array->child=newitem;
    else newitem->prev->next=newitem;
}
/* 用新元素替换JSON的数组中wihch位置的元素 */
void   cJSON_ReplaceItemInArray(cJSON *array,int which,cJSON *newitem)
{
    cJSON *c=array->child;
    while (c && which>0) c=c->next,which--;
    if (!c) return;
    newitem->next=c->next;
    newitem->prev=c->prev;
    if (newitem->next) newitem->next->prev=newitem;
    if (c==array->child) array->child=newitem;
    else newitem->prev->next=newitem;
	
    c->next=c->prev=0;
    cJSON_Delete(c);
}
/* 用新元素替换JSON的对象中名为string的元素 */
void   cJSON_ReplaceItemInObject(cJSON *object,const char *string,cJSON *newitem)
{
    int i=0;
    cJSON *c=object->child;
    while(c && cJSON_strcasecmp(c->string,string))i++,c=c->next;
    if(c) {
        newitem->string=cJSON_strdup(string);
        cJSON_ReplaceItemInArray(object,i,newitem);
    }
}

/* 创建基本类型的JSON。。Create basic types: */
cJSON *cJSON_CreateNull(void)
{
    cJSON *item=cJSON_New_Item();
    if(item)item->type=cJSON_NULL;
    return item;
}
cJSON *cJSON_CreateTrue(void)
{
    cJSON *item=cJSON_New_Item();
    if(item)item->type=cJSON_True;
    return item;
}
cJSON *cJSON_CreateFalse(void)
{
    cJSON *item=cJSON_New_Item();
    if(item)item->type=cJSON_False;
    return item;
}
cJSON *cJSON_CreateBool(int b)
{
    cJSON *item=cJSON_New_Item();
    if(item)item->type=b?cJSON_True:cJSON_False;
    return item;
}
cJSON *cJSON_CreateNumber(double num)
{
    cJSON *item=cJSON_New_Item();
    if(item) {
        item->type=cJSON_Number;
        item->valuedouble=num;
        item->valueint=(int)num;
    }
    return item;
}
cJSON *cJSON_CreateString(const char *string)
{
    cJSON *item=cJSON_New_Item();
    if(item) {
        item->type=cJSON_String;
        item->valuestring=cJSON_strdup(string);
    }
    return item;
}
cJSON *cJSON_CreateArray(void)
{
    cJSON *item=cJSON_New_Item();
    if(item)item->type=cJSON_Array;
    return item;
}
cJSON *cJSON_CreateObject(void)
{
    cJSON *item=cJSON_New_Item();
    if(item)item->type=cJSON_Object;
    return item;
}
cJSON *cJSON_CreateIntArray(const int *numbers,int count)
{
    int i;
    cJSON *n=0,*p=0,*a=cJSON_CreateArray();
    for(i=0; a && i<count; i++) {
        n=cJSON_CreateNumber(numbers[i]);
        if(!i)a->child=n;
        else suffix_object(p,n);
        p=n;
    }
    return a;
}
cJSON *cJSON_CreateFloatArray(const float *numbers,int count)
{
    int i;
    cJSON *n=0,*p=0,*a=cJSON_CreateArray();
    for(i=0; a && i<count; i++) {
        n=cJSON_CreateNumber(numbers[i]);
        if(!i)a->child=n;
        else suffix_object(p,n);
        p=n;
    }
    return a;
}
cJSON *cJSON_CreateDoubleArray(const double *numbers,int count)
{
    int i;
    cJSON *n=0,*p=0,*a=cJSON_CreateArray();
    for(i=0; a && i<count; i++) {
        n=cJSON_CreateNumber(numbers[i]);
        if(!i)a->child=n;
        else suffix_object(p,n);
        p=n;
    }
    return a;
}
cJSON *cJSON_CreateStringArray(const char **strings,int count)
{
    int i;
    cJSON *n=0,*p=0,*a=cJSON_CreateArray();
    for(i=0; a && i<count; i++) {
        n=cJSON_CreateString(strings[i]);
        if(!i)a->child=n;
        else suffix_object(p,n);
        p=n;
    }
    return a;
}

/* 复制cJSON
   参数: item: 要复制的cJSON
         recurse:是否递归的复制. 非0表示递归的复制
   返回值:cJSON的副本*/
cJSON *cJSON_Duplicate(cJSON *item,int recurse)
{
    cJSON *newitem,*cptr,*nptr=0,*newchild;
    /* 参数无效 */
    if (!item) return 0;
    
    newitem=cJSON_New_Item(); // Create new item 
    if (!newitem) return 0;

	/* 复制所有的值*/
    newitem->type=item->type&(~cJSON_IsReference),newitem->valueint=item->valueint,newitem->valuedouble=item->valuedouble;
    if (item->valuestring)	{
        newitem->valuestring=cJSON_strdup(item->valuestring);
        if (!newitem->valuestring)	{
            cJSON_Delete(newitem);
            return 0;
        }
    }
    if (item->string)		{
        newitem->string=cJSON_strdup(item->string);
        if (!newitem->string)		{
            cJSON_Delete(newitem);
            return 0;
        }
    }
    /* 如果非递归,那么我们就完成了 */
    if (!recurse) return newitem;

	/* Walk the ->next chain for the child. */
    cptr=item->child;
    while (cptr) {
        newchild=cJSON_Duplicate(cptr,1);		/* Duplicate (with recurse) each item in the ->next chain */
        if (!newchild) {
            cJSON_Delete(newitem);
            return 0;
        }
        if (nptr)	{
            nptr->next=newchild,newchild->prev=nptr;    /* If newitem->child already set, then crosswire ->prev and ->next and move on */
            nptr=newchild;
        } else		{
            newitem->child=newchild;    /* Set newitem->child and move to it */
            nptr=newchild;
        }
        cptr=cptr->next;
    }
    return newitem;
}

//简缩JSON文本(去掉空白字符和注释)
void cJSON_Minify(char *json)
{
    char *into=json;
    while (*json) {
        if (*json==' ') json++;
        else if (*json=='\t') json++;	/* 空白字符. */
        else if (*json=='\r') json++;
        else if (*json=='\n') json++;
        else if (*json=='/' && json[1]=='/')  while (*json && *json!='\n') json++;	/* 双斜杠注释,行结束. */
        else if (*json=='/' && json[1]=='*') {
            while (*json && !(*json=='*' && json[1]=='/')) json++;    /* 多行注释. */
            json+=2;
        } else if (*json=='\"') {
            *into++=*json++;    /* 字符串字面值,\“敏感  */
            while (*json && *json!='\"') {
                if (*json=='\\') *into++=*json++;
                *into++=*json++;
            }*into++=*json++;
        } else *into++=*json++;			/* All other characters. */
    }
    *into=0;	/* and null-terminate. */
}
