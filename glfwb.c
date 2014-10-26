// Data processing toolkit for BORT sensors, v1.0 - implemented with GLFW3
// Based on glfw data processing toolkit v1.1 (v1.0 was on GLUT)
// Compile with
// gcc -o glfwb glfwb.c -lGL -lGLU -lglfw3 -lX11 -lXxf86vm -lXrandr -lpthread -lXi -lm
// BGO IPE RAS
// for internal use only

#include <GLFW/glfw3.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <sys/time.h>

// GLFW patch
GLFWwindow* window;
unsigned char Redisplay=1;
int screen_width;
int screen_height;
struct GLFWvidmode *current_vmode;
//---

const float hscale = 0.15F;
const float vscale = 0.06F;

float wnd_part = 6.0f;
float vshift = 0.0f;
float vf = 0.0f;
float vt = 0.0f;
float vinc = 0.1f;

int wbeg;
int wsize;
float dscale;
float dtrim;

float mpos;
float mposy;

int mousex;
int mousey;
int cpos;

float data[86400][5]; //0,1 - data, 2,3 - estimation data, 5 - temporary

// Bort sensors management variables declaration
float zero[86400][2]; // zero curve 0,1 - channels
int zp[3600][5]; 	// zero points. 0 - start, 1 - end, 2 - zero interval start,
					// 3 - zero interval end (rel. to zp start), 4 - pos/neg flag (0 - next data on first channel is positive, and on second - negative)
int nzp; // count of zero points
// ---

// undo variables ---
float undo[86400][2][20];
int undo_count=0;
//---

// selection variables ---
unsigned int sel_beg;
unsigned int sel_end;
unsigned int selected=0;
unsigned int est_type=0;
// ---

GLfloat x;
GLfloat y;
GLfloat ox;
GLfloat oy;
GLfloat dx;

char ss[50];
unsigned char key_code;

struct ChrFont
{
    unsigned short hSize;
    unsigned short fSize;
    unsigned short nChar;
    unsigned char fChar;
    signed char uMargin;
    signed char lMargin;
    unsigned short mHeight;
    unsigned short cOff[256];
    unsigned char cWidth[256];
    unsigned char mWidth;
    char *fData;
    unsigned int dSize;
};

struct ChrFont Font;

// Flags-----
unsigned char dHelp = 1;    // Display help
unsigned char dGraph = 3;   // Display 1 - first channel, 2 - second channel, 3 - both
unsigned char dStatus = 1;  // Display status information
unsigned char dEstimation = 1;  // Display estimation
unsigned char dZeroCurve=1;		// Display zero curve (Bort sensors management)

unsigned char cActive = 1;   // Active channel 1 - first, 2 - second, 3 - both
unsigned char fBusy = 1;    // Busy flag
unsigned char tEnter = 0;	// Text entering
unsigned char nEnter = 0;	// Number entering
// Flags-----

// Text/number entering variables
char te[55];
char name_str[10];
// ---

char *main_file_name;
char Busy_Str[16];
int timer_count = 0;

void WriteLog(char *logstr)
{
    FILE *f;
    f = fopen("glfw.log","at");
    fprintf(f,"%s\n",logstr);
    fclose(f);
}

// timer implementation
struct timeval tv1,tv2,dtv;
void time_start()
{
    gettimeofday(&tv1, NULL);
}
long time_stop()
{
    gettimeofday(&tv2, NULL);
    dtv.tv_sec= tv2.tv_sec -tv1.tv_sec;
    dtv.tv_usec=tv2.tv_usec-tv1.tv_usec;
    if(dtv.tv_usec<0)
    {
        dtv.tv_sec--; dtv.tv_usec+=1000000;
    }

    return dtv.tv_sec*1000+dtv.tv_usec/1000;
}
// end timer---

void load_chr_font(char *fname) // Borland .chr font loader (simple and brutal)
{
    FILE *f;

    f = fopen(fname,"rb");

    unsigned char buf[20];
    fread(buf,1,4,f);   // PK#8#8
    while (buf[0] != 0x1A) { fread(&buf[0],1,1,f); } // Copyrights

    fread(&Font.hSize,2,1,f);    // header size
    fread(buf,1,4,f);   // font name
    fread(&Font.fSize,2,1,f);    // font size
    fseek(f,Font.hSize+1,SEEK_SET);

    fread(&Font.nChar,2,1,f);
    fread(&buf[0],1,1,f);
    fread(&Font.fChar,1,1,f);

    unsigned short fofs;
    fread(&fofs,2,1,f);
    fread(&buf[0],1,1,f);

    fread(&Font.uMargin,1,1,f);
    fread(buf,1,1,f);
    fread(&Font.lMargin,1,1,f);
    fread(buf,1,5,f);

    unsigned int i;
    for (i=0; i<Font.nChar; i++)
    {
        fread(&Font.cOff[i],2,1,f);
    }
    for (i=0; i<Font.nChar; i++)
    {
        fread(&Font.cWidth[i],1,1,f);
    }

    long int c1;
    c1 = ftell(f);
    fseek(f,0L,SEEK_END);
    long int c2;
    c2 = ftell(f);
    fseek(f,c1,SEEK_SET);

    Font.fData=malloc(c2-c1);
    Font.dSize = c2-c1;
    fread(Font.fData,1,Font.dSize,f);
    fclose(f);

    Font.mWidth = Font.cWidth[0];
    Font.mHeight = Font.uMargin-Font.lMargin;
    for (i=0; i<Font.nChar; i++)
    {
        if (Font.mWidth < Font.cWidth[i]) { Font.mWidth = Font.cWidth[i]; }
    }
}

void DrawChar(unsigned char code, struct ChrFont fnt, float x, float y, float sx, float sy)
{
    float px;
    float py;
    float ix;
    float iy;
    unsigned char dend=0;

    unsigned char b1;
    unsigned char b2;

    signed char k1;
    signed char k2;

    unsigned short Off=fnt.cOff[code];

    while (dend==0)
    {
        b1 = fnt.fData[Off];
        b2 = fnt.fData[Off+1];
        if (((b1 & 0x80) == 0)&&((b2 & 0x80) == 0))
        {
            dend = 1;
            break;
        }
        if (((b1 & 0x80) == 0x80)&&((b2 & 0x80) == 0))
        {
            k1 = b1 & 0x7F; k2 = b2 & 0x7F;
            if ((b1 & 0x40) == 0x40) { k1 = b1 | 0x80; }
            if ((b2 & 0x40) == 0x40) { k2 = b2 | 0x80; }

            px = ((float)k1 / fnt.mWidth)*sx;
            py = ((float)k2 / fnt.mHeight)*sy;
        }
        if (((b1 & 0x80) == 0x80)&&((b2 & 0x80) == 0x80))
        {
            k1 = b1 & 0x7F; k2 = b2 & 0x7F;
            if ((b1 & 0x40) == 0x40) { k1 = k1 | 0x80; }
            if ((b2 & 0x40) == 0x40) { k2 = k2 | 0x80; }

            ix = ((float)k1 / fnt.mWidth)*sx;
            iy = ((float)k2 / fnt.mHeight)*sy;
            glBegin(GL_LINES);
            glVertex2f(x+px,y+py);
            glVertex2f(x+ix,y+iy);
            glEnd();
            px = ix; py = iy;
        }
        Off += 2;
    }
}

void glDrawWindow(float x1, float y1, float x2, float y2)
{
	glEnable(GL_BLEND);
	glColor4f(0.0,0.0,0.0,0.2);
	glBegin(GL_QUADS);
	glVertex2f(x1+0.02,y1-0.02);		// Shadow
	glVertex2f(x2+0.02,y1-0.02);
	glVertex2f(x2+0.02,y2-0.02);
	glVertex2f(x1+0.02,y2-0.02);
	glColor4f(0.7,0.7,0.0,1.0);	// Window border
	glVertex2f(x1,y1);
	glVertex2f(x2,y1);
	glVertex2f(x2,y2);
	glVertex2f(x1,y2);
	glEnd();
	glLineWidth(3);
	glBegin(GL_LINES);
	glColor4f(1.0,1.0,0.0,1.0);
	glVertex2f(x1,y1);
	glVertex2f(x2,y1);
	glVertex2f(x1,y1);
	glVertex2f(x1,y2);
	glColor4f(0.3,0.3,0.0,1.0);
	glVertex2f(x2,y1);
	glVertex2f(x2,y2);
	glVertex2f(x2,y2);
	glVertex2f(x1,y2);
	glEnd();
	glDisable(GL_BLEND);
}

void glDrawEditBar(float x1, float y1, float w)
{
	glBegin(GL_QUADS);
	glVertex2f(x1,y1);
	glVertex2f(x1+w,y1);
	glVertex2f(x1+w,y1-0.1);
	glVertex2f(x1,y1-0.1);
	glEnd();
}
void DrawText(char *tx, struct ChrFont fnt, float x, float y, float sx, float sy)
{
    float dx;
    float dy;
    unsigned char t;
    int i=0;

    dx = x; dy = y;

    while (i < strlen(tx))
    {
        if ((unsigned char)tx[i] >= fnt.fChar)
        {
            t = (unsigned char)tx[i] - fnt.fChar;
            DrawChar(t,fnt,dx,dy,sx,sy);
            dx += ((float)fnt.cWidth[t] / (float)fnt.mWidth) * sx;
        }
        i++;
    }
}

void Draw( void )
{
    int i;
    glClear(GL_COLOR_BUFFER_BIT);
    glColor3f(0.0f, 0.0f, 0.0f);
    glLineWidth(3);
    glBegin(GL_LINES);
    glVertex2f(-1.0, dtrim);
    glVertex2f(1.0f, dtrim);
    glEnd();

    if ((dGraph & 0x01) == 0x01)
    {
        glColor3f(0.0f,0.0f,1.0f);
        i = wbeg;
        dx = 2.0f / wsize;
        ox = -1.0f;
        oy = data[i][0]*dscale + dtrim;
        i++;
        x = ox+dx;
        glLineWidth(1);
        while (i < (wbeg+wsize))
        {
            if (i > 86399) break;
            y = data[i][0]*dscale + dtrim;
            if (selected==2)
            {
                if ((i > sel_end)||(i < sel_beg)) { glLineWidth(1); }
                if ((i >= sel_beg)&&(i <= sel_end)) { glLineWidth(3); }
            }
            glBegin(GL_LINES);
            glVertex2f(ox,oy);
            glVertex2f(x,y);
            glEnd();
            ox = x; oy = y;
            x = x+dx;
            i++;
        }
    }

    if ((dGraph & 0x02) == 0x02)
    {
        glColor3f(0.0f,0.5f,0.0f);
        i = wbeg;
        dx = 2.0f / wsize;
        ox = -1.0f;
        oy = data[i][1]*dscale + dtrim;
        i++;
        x = ox+dx;
        glLineWidth(1);
        while (i < (wbeg+wsize))
        {
            if (i > 86399) break;
            y = data[i][1]*dscale + dtrim;
            if (selected==2)
            {
                if ((i > sel_end)||(i < sel_beg)) { glLineWidth(1); }
                if ((i >= sel_beg)&&(i <= sel_end)) { glLineWidth(3); }
            }
            glBegin(GL_LINES);
            glVertex2f(ox,oy);
            glVertex2f(x,y);
            glEnd();
            ox = x; oy = y;
            x = x+dx;
            i++;
        }
    }

    if (dZeroCurve==1)
    {
    	// first display marked zero intervals
    	dx = 2.0f/wsize;
    	glLineWidth(1);
    	glColor3f(0.0f,0.0f,0.0f);
    	glEnable(GL_LINE_STIPPLE);
		glLineStipple(1,0x00FF);
    	if (nzp>0)
    	{
			for (i=0;i<nzp;i++)
			{
				if ((zp[i][0] > wbeg) && (zp[i][0] < (wbeg+wsize)))
				{
					x = (zp[i][0]-wbeg)*dx - 1.0f;
					glBegin(GL_LINES);
					glVertex2f(x,-1.0f);
					glVertex2f(x,1.0f);
					glEnd();
					glEnable(GL_BLEND);
					glColor4f(1.0,0.0,0.0,0.3);
					glBegin(GL_QUADS);
					glVertex2f(x,1.0f);
					glVertex2f((zp[i][0]+zp[i][2]-wbeg)*dx-1.0f,1.0f);
					glVertex2f((zp[i][0]+zp[i][2]-wbeg)*dx-1.0f,-1.0f);
					glVertex2f(x,-1.0f);
					glColor4f(0.0,1.0,0.0,0.3);
					glVertex2f((zp[i][0]+zp[i][2]-wbeg)*dx-1.0f,1.0f);
					glVertex2f((zp[i][0]+zp[i][3]-wbeg)*dx-1.0f,1.0f);
					glVertex2f((zp[i][0]+zp[i][3]-wbeg)*dx-1.0f,-1.0f);
					glVertex2f((zp[i][0]+zp[i][2]-wbeg)*dx-1.0f,-1.0f);
					glColor4f(1.0,0.0,0.0,0.3);
					glVertex2f((zp[i][0]+zp[i][3]-wbeg)*dx-1.0f,1.0f);
					glVertex2f((zp[i][1]-wbeg)*dx-1.0f,1.0f);
					glVertex2f((zp[i][1]-wbeg)*dx-1.0f,-1.0f);
					glVertex2f((zp[i][0]+zp[i][3]-wbeg)*dx-1.0f,-1.0f);
					glEnd();
					glDisable(GL_BLEND);
					glColor3f(0.0,0.0,0.0);
					glLineWidth(2);
					if (zp[i][4]==0)
						DrawText("N-P",Font,x+(((zp[i][1]-zp[i][0])*dx)/2)-0.02,0.95,hscale/1.5,vscale/1.5);
					else
						DrawText("P-N",Font,x+(((zp[i][1]-zp[i][0])*dx)/2)-0.02,0.95,hscale/1.5,vscale/1.5);
					glLineWidth(1);
				}
				glColor3f(0.0f,0.0f,0.0f);
				if ((zp[i][1] > wbeg) && (zp[i][1] < (wbeg+wsize)))
				{
					x = (zp[i][1]-wbeg)*dx - 1.0f;
					glBegin(GL_LINES);
					glVertex2f(x,-1.0f);
					glVertex2f(x,1.0f);
					glEnd();
				}
			}
    	}

		// then let's display zero curve
		glColor3f(0.3f,0.3f,0.3f);
		glLineStipple(1,0xFFFF);
		glDisable(GL_LINE_STIPPLE);
		if ((dGraph & 0x01) == 0x01)
		{
			i = wbeg;
			x = -1.0f;
			glLineWidth(1);
			glBegin(GL_LINE_STRIP);
			while (i < (wbeg+wsize))
			{
				if (i > 86399) break;
				y = zero[i][0]*dscale + dtrim;
				glVertex2f(x,y);
				x = x+dx;
				i++;
			}
			glEnd();
		}
		if ((dGraph & 0x02) == 0x02)
		{
			i = wbeg;
			x = -1.0f;
			glLineWidth(1);
			glBegin(GL_LINE_STRIP);
			while (i < (wbeg+wsize))
			{
				if (i > 86399) break;
				y = zero[i][1]*dscale + dtrim;
				glVertex2f(x,y);
				x = x+dx;
				i++;
			}
			glEnd();
		}
    }

    if ((est_type > 0)&&(selected==2))
    {
        glColor3f(1.0f,0.0f,0.0f);
        if ((cActive & 0x01) == 0x01)
        {
            glLineWidth(2);
            glBegin(GL_LINE_STRIP);
            i = wbeg;
            dx = 2.0f / wsize;
            x = -1.0f;
            while (i < (wbeg+wsize))
            {
                if (i > 86399) break;
                if ((i >= sel_beg)&&(i < sel_end))
                {
                    y = data[i][2] * dscale + dtrim;
                    glVertex2f(x,y);
                }
                x = x+dx;
                i++;
            }
            glEnd();
        }
        if ((cActive & 0x02) == 0x02)
        {
            glLineWidth(2);
            glBegin(GL_LINE_STRIP);
            i = wbeg;
            dx = 2.0f / wsize;
            x = -1.0f;
            while (i < (wbeg+wsize))
            {
                if (i > 86399) break;
                if ((i >= sel_beg)&&(i < sel_end))
                {
                    y = data[i][3] * dscale + dtrim;
                    glVertex2f(x,y);
                }
                x = x+dx;
                i++;
            }
            glEnd();
        }
    }

    // mouse cursor drawing
    if ((nEnter == 0) && (tEnter == 0))
    {
		glColor3f(0.0f,0.0f,0.0f);
		glBegin(GL_LINES);
		glVertex2f(mpos,-1.0f);
		glVertex2f(mpos,1.0f);
		glVertex2f(-1.0f,mposy);
		glVertex2f(1.0f,mposy);
		glEnd();
	}
	// ---

    glLineWidth(2);

    if (dStatus == 1)
    {
        char est_str[80];
        switch (est_type)
        {
            case 0:
            {
                sprintf(est_str,"None");
                break;
            }
            case 1:
            {
                sprintf(est_str,"First-last line");
                break;
            }
            case 2:
            {
                sprintf(est_str,"Linear regression (least squares)");
                break;
            }
            case 3:
            {
                sprintf(est_str,"Exponential regression (least squares)");
                break;
            }
            case 4:
            {
                sprintf(est_str,"Tail");
                break;
            }
            case 5:
            {
                sprintf(est_str,"Face");
                break;
            }
            case 6:
            {
                sprintf(est_str,"Sliding average");
                break;
            }
            case 7:
            {
                sprintf(est_str,"Sliding median");
                break;
            }
            case 8:
            {
                sprintf(est_str,"Visual shift");
                break;
            }
            case 9:
            {
				sprintf(est_str,"Visual multiplication");
				break;
			}
        }
        sprintf(ss,"ESTIM = %s",est_str);
        DrawText(ss,Font,-1.0F,0.95F,hscale,vscale);
        switch (cActive)
        {
            case 1:
            {
                sprintf(est_str,"First");
                break;
            }
            case 2:
            {
                sprintf(est_str,"Second");
                break;
            }
            case 3:
            {
                sprintf(est_str,"Both");
                break;
            }
        }
        sprintf(ss,"ACTIVE = %s",est_str);
        DrawText(ss,Font,-1.0F,0.9F,hscale,vscale*0.9f);
        sprintf(ss,"SBEG = %02d:%02d:%02d",sel_beg/3600, (sel_beg%3600)/60, (sel_beg%3600)%60);
        DrawText(ss,Font,-1.0F,0.85F,hscale,vscale*0.9f);
        sprintf(ss,"SEND = %02d:%02d:%02d", sel_end/3600, (sel_end%3600)/60, (sel_end%3600)%60);
        DrawText(ss,Font,-1.0F,0.8F,hscale,vscale*0.9f);
        sprintf(ss,"POS = %02d:%02d:%02d", cpos/3600, (cpos%3600)/60, (cpos%3600)%60);
        DrawText(ss,Font,-1.0F,0.75F,hscale,vscale*0.9f);
        sprintf(ss,"V1 = %f; V2 = %f",data[cpos][0],data[cpos][1]);
//        sprintf(ss,"KEY = %X", key_code);
        DrawText(ss,Font,-1.0F,0.7F,hscale,vscale*0.9f);
// bottom status bar drawing
        if (selected==2)
        {
            switch (est_type)
            {
                case 6:
                case 7:
                {
                    sprintf(ss,"WNDPART = %f; WND = %d sec; Ctrl-W = wndpart+0.1 Ctrl-S = wndpart-0.1",wnd_part,(int)round((sel_end-sel_beg)/wnd_part));
                    DrawText(ss,Font,-1.0f,-0.95f,hscale/1.5,vscale/1.5);
                    break;
                }
                case 8:
                {
                    sprintf(ss,"VF = %f; VT = %f; VINC = %f; Ctrl-W - Up, Ctrl-S - Down, Alt-W/S - Face, Ctrl-Alt-W/S - Tail",vf,vt,vinc);
                    DrawText(ss,Font,-1.0f,-0.95f,hscale/1.5,vscale/1.5);
                    break;
                }
                case 9:
                {
                    sprintf(ss,"MUL = %f; VINC = %f; Ctrl-W - Up, Ctrl-S - Down",vt,vinc);
                    DrawText(ss,Font,-1.0f,-0.95f,hscale/1.5,vscale/1.5);
                    break;
				}
            }
        }
    }

    if (dHelp == 1)
    {
		glEnable(GL_BLEND);
		glColor4f(0.0,0.0,0.0,0.05);
        for (i=0;i<5;i++)
        {
			glBegin(GL_QUADS);
			glVertex2f(0.6+((float)i*0.005),1.0-((float)i*0.005));
			glVertex2f(1.0-((float)i*0.005),1.0-((float)i*0.005));
			glVertex2f(1.0-((float)i*0.005),-0.05+((float)i*0.005));
			glVertex2f(0.6+((float)i*0.005),-0.05+((float)i*0.005));
			glEnd();
		}
		glDisable(GL_BLEND);
        glColor3f(0.0,0.0,0.0);
        float h;
        float v;
        h = hscale/1.8;
        v = vscale/1.5;
        DrawText("Brief help:",Font,0.65,0.95,h,v);
        DrawText("D - slide right",Font,0.65,0.9,h,v);
        DrawText("A - slide left",Font,0.65,0.85,h,v);
        DrawText("W - trim up",Font,0.65,0.8,h,v);
        DrawText("S - trim down",Font,0.65,0.75,h,v);
        DrawText("Shift-D - horizontal zoom in",Font,0.65,0.7,h,v);
        DrawText("Shift-A - horizontal zoom out",Font,0.65,0.65,h,v);
        DrawText("Shift-W - vertical zoom in",Font,0.65,0.6,h,v);
        DrawText("Shift-S - vertical zoom out",Font,0.65,0.55,h,v);
        DrawText("F - patch estimation",Font,0.65,0.5,h,v);
        DrawText("Shift-F - substract estimation",Font,0.65,0.45,h,v);
        DrawText("C - select active channel",Font,0.65,0.4,h,v);
        DrawText("1..9 - estimation type",Font,0.65,0.35,h,v);
        DrawText("U - undo",Font,0.65,0.3,h,v);
        DrawText("X - toggle status",Font,0.65,0.25,h,v);
        DrawText("G - toggle channel display",Font,0.65,0.2,h,v);
        DrawText("H - toggle help",Font,0.65,0.15,h,v);
        DrawText("---",Font,0.65,0.1,h,v);
        DrawText("CTRL-Q - Exit and discard changes",Font,0.65,0.05,h,v);
        DrawText("F5 - Save changes",Font,0.65,0.0,h,v);
    }
    if (dHelp == 2)
    {
		glEnable(GL_BLEND);
		glColor4f(0.0,0.0,0.0,0.05);
        for (i=0;i<5;i++)
        {
			glBegin(GL_QUADS);
			glVertex2f(0.6+((float)i*0.005),1.0-((float)i*0.005));
			glVertex2f(1.0-((float)i*0.005),1.0-((float)i*0.005));
			glVertex2f(1.0-((float)i*0.005),0.1+((float)i*0.005));
			glVertex2f(0.6+((float)i*0.005),0.1+((float)i*0.005));
			glEnd();
		}
		glDisable(GL_BLEND);
        glColor3f(0.0,0.0,0.0);
        float h;
        float v;
        h = hscale/1.8;
        v = vscale/1.5;
  		DrawText("Brief help:",Font,0.65,0.95,h,v);
  		DrawText("Z - mark zero point",Font,0.65,0.9,h,v);
  		DrawText("Shift-Z - refresh zero curve",Font,0.65,0.85,h,v);
  		DrawText("P - apply zero curve to data",Font,0.65,0.8,h,v);
  		DrawText("J - show/hide zero curve",Font,0.65,0.75,h,v);
  		DrawText("L - load zero curve",Font,0.65,0.7,h,v);
  		DrawText("DEL - delete zero point mark",Font,0.65,0.65,h,v);
  		DrawText("I - invert pos/neg order (at cursor)",Font,0.65,0.6,h,v);
  		DrawText("Shift-I - invert pos/neg order",Font,0.65,0.55,h,v);
  		DrawText("F1 - one hour per screen zoom",Font,0.65,0.5,h,v);
  		DrawText("F2 - one day per screen zoom",Font,0.65,0.45,h,v);
  		DrawText("F3 - 6 hour per screen zoom",Font,0.65,0.4,h,v);
  		DrawText("F4 - 12 hour per screen zoom",Font,0.65,0.35,h,v);
  		DrawText("T - edit values immediately",Font,0.65,0.3,h,v);
  		DrawText("Ctrl-A - select all",Font,0.65,0.25,h,v);
  		DrawText("Ctrl-0 - Discard odd",Font,0.65,0.2,h,v);
  		DrawText("Ctrl-1 - Discard even",Font,0.65,0.15,h,v);
    }

    if (fBusy == 1)
    {
        DrawText(Busy_Str,Font,0.75,-0.95,hscale,vscale);
    }

	if (nEnter == 1)	// number entering window drawing
	{
		glDrawWindow(-0.5,0.3,0.5,0.0);
		glColor3f(0.0,0.0,0.0);
		glDrawEditBar(-0.45,0.2,0.8);
		glColor3f(1.0,1.0,1.0);
		glLineWidth(2);
		if (strlen(te) > 0) DrawText(te,Font,-0.4,0.12,hscale,vscale);
	}
    glfwSwapBuffers(window);
}

void timer()
{
    if (fBusy == 1)
    {
        long tmi;

        tmi = time_stop();
        if (tmi > 100)
        {
            if (timer_count == 1) { sprintf(Busy_Str, "BUSY *---"); }
            if (timer_count == 2) { sprintf(Busy_Str, "BUSY -*--"); }
            if (timer_count == 3) { sprintf(Busy_Str, "BUSY --*-"); }
            if (timer_count == 0) { sprintf(Busy_Str, "BUSY ---*"); }
            timer_count++;
            if (timer_count == 4) timer_count=0;
            Draw();
            time_start();
        }
    }
}

float get_median(int pos1, int pos2, int nn)    // returns median of choosen interval in ion data (pos1,pos2 - interval, nn - channel number 0 or 1)
{
    int i;
    int j;
    float median;
    int c=pos2-pos1;

    for (i=pos1; i<pos2; i++)
    {
        data[i-pos1][4] = data[i][nn];
    }
    for (i=0; i < (c/2+1); i++)	//optimized!
    {
        j = (i+1);
        while (j < c)
        {
            if (data[i][4] < data[j][4])
            {
                median = data[i][4];
                data[i][4] = data[j][4];
                data[j][4] = median;
            }
            j++;
        }
    }
    median = data[(c/2)][4];

    return median;
}

float get_mean(int pos1, int pos2, int nn)
{
    int i;
    float mean=0.0f;

    for (i=pos1;i<pos2;i++)
    {
        mean += data[i][nn];
    }
    mean /= (pos2-pos1);
    return mean;
}

void make_estimation()
{
    fBusy = 1;
    int i;
    switch (est_type)
    {
        case 0:
        {
            break;
        }
        case 1:     // makes line from sel_beg to sel_end using first and last data entries
        {
            float k;
            float b;

            if ((cActive & 0x01)==0x01) // first channel
            {
                k = (data[sel_end][0] - data[sel_beg][0])/((float)sel_end-(float)sel_beg);  // k = (y2-y1)/(x2-x1)
                b = data[sel_beg][0] - (k*(float)sel_beg);
                for (i=sel_beg;i<sel_end;i++)
                {
                    data[i][2] = (k*(float)i) + b;
                }
            }

            if ((cActive & 0x02)==0x02) // second channel
            {
                k = (data[sel_end][1] - data[sel_beg][1])/((float)sel_end-(float)sel_beg);  // k = (y2-y1)/(x2-x1)
                b = data[sel_beg][1] - (k*(float)sel_beg);
                for (i=sel_beg;i<sel_end;i++)
                {
                    data[i][3] = (k*(float)i) + b;
                }
            }
            break;
        }
        case 2:     // Less squares linear estimation
        {
            long double a=0.0f;
            long double b=0.0f;
            long double mx=0.0f;
            long double mx2=0.0f;
            long double my=0.0f;
            long double mxy=0.0f;

            if ((cActive & 0x01)==0x01)
            {
                for (i=sel_beg;i<sel_end;i++)
                {
                    mxy += ((long double)i*(long double)data[i][0]);
                    my += (long double)data[i][0];
                    mx += (long double)i;
                    mx2 += (long double)i * (long double)i;
                    timer();
                }
                mxy /= ((long double)sel_end-(long double)sel_beg);
                my /= ((long double)sel_end-(long double)sel_beg);
                mx /= ((long double)sel_end-(long double)sel_beg);
                mx2 /= ((long double)sel_end-(long double)sel_beg);
                b = (mxy - (mx*my))/(mx2 - (mx*mx));
                a = my - (b*mx);

                for (i=sel_beg;i<sel_end;i++)
                {
                    data[i][2] = (float)a + (float)b*(float)i;
                }
            }

            if ((cActive & 0x02)==0x02)
            {
                mx = 0.0f;
                my = 0.0f;
                mxy = 0.0f;
                mx2 = 0.0f;
                for (i=sel_beg;i<sel_end;i++)
                {
                    mxy += ((long double)i*(long double)data[i][1]);
                    my += (long double)data[i][1];
                    mx += (long double)i;
                    mx2 += (long double)i * (long double)i;
                    timer();
                }
                mxy /= ((long double)sel_end-(long double)sel_beg);
                my /= ((long double)sel_end-(long double)sel_beg);
                mx /= ((long double)sel_end-(long double)sel_beg);
                mx2 /= ((long double)sel_end-(long double)sel_beg);
                b = (mxy - (mx*my))/(mx2 - (mx*mx));
                a = my - (b*mx);

                for (i=sel_beg;i<sel_end;i++)
                {
                    data[i][3] = (float)a + (float)b*(float)i;
                }
            }
            break;
        }
        case 3:     // Exponent estimation
        {
            long double a=0.0f;
            long double b=0.0f;
            long double mx=0.0f;
            long double mx2=0.0f;
            long double my=0.0f;
            long double mxy=0.0f;

            float min_data=0;

            if ((cActive & 0x01)==0x01)
            {
                min_data = data[sel_beg][0];
                for (i=(sel_beg+1);i<sel_end;i++)
                {
                    if (min_data > data[i][0]) { min_data = data[i][0]; }
                }
                for (i=sel_beg;i<sel_end;i++)
                {
                    mxy += ((long double)i*logl((long double)(data[i][0] - min_data + 0.1)));
                    my += logl((long double)(data[i][0] - min_data + 0.1));
                    mx += (long double)i;
                    mx2 += (long double)i * (long double)i;
                    timer();
                }
                mxy /= ((long double)sel_end-(long double)sel_beg);
                my /= ((long double)sel_end-(long double)sel_beg);
                mx /= ((long double)sel_end-(long double)sel_beg);
                mx2 /= ((long double)sel_end-(long double)sel_beg);
                b = (mxy - (mx*my))/(mx2 - (mx*mx));
                a = expl(my - (b*mx));

                for (i=sel_beg;i<sel_end;i++)
                {
                    data[i][2] = ((float)a*(float)expl(b*(long double)i)) + min_data - 0.1;
                }
            }

            if ((cActive & 0x02)==0x02)
            {
                mx = 0.0f;
                my = 0.0f;
                mxy = 0.0f;
                mx2 = 0.0f;
                min_data = data[sel_beg][1];
                for (i=(sel_beg+1);i<sel_end;i++)
                {
                    if (min_data > data[i][1]) { min_data = data[i][1]; }
                }
                for (i=sel_beg;i<sel_end;i++)
                {
                    mxy += ((long double)i*logl((long double)(data[i][1] - min_data + 0.1)));
                    my += logl((long double)(data[i][1] - min_data + 0.1));
                    mx += (long double)i;
                    mx2 += (long double)i * (long double)i;
                    timer();
                }
                mxy /= ((long double)sel_end-(long double)sel_beg);
                my /= ((long double)sel_end-(long double)sel_beg);
                mx /= ((long double)sel_end-(long double)sel_beg);
                mx2 /= ((long double)sel_end-(long double)sel_beg);
                b = (mxy - (mx*my))/(mx2 - (mx*mx));
                a = expl(my - (b*mx));

                for (i=sel_beg;i<sel_end;i++)
                {
                    data[i][3] = ((float)a*(float)expl(b*(long double)i)) + min_data - 0.1;
                }
            }

            break;
        }
        case 4:     // Tail - fills all selection by first data entry
        {
            if ((cActive & 0x01)==0x01) for (i=sel_beg;i<sel_end;i++) { data[i][2] = data[sel_beg][0]; }
            if ((cActive & 0x02)==0x02) for (i=sel_beg;i<sel_end;i++) { data[i][3] = data[sel_beg][1]; }
            break;
        }
        case 5:     // Face - fills all selection by last data entry
        {
            if ((cActive & 0x01)==0x01) for (i=sel_beg;i<sel_end;i++) { data[i][2] = data[sel_end][0]; }
            if ((cActive & 0x02)==0x02) for (i=sel_beg;i<sel_end;i++) { data[i][3] = data[sel_end][1]; }
            break;
        }
        case 6:     // Sliding average
        {
            if ((sel_end-sel_beg) < (wnd_part*3)) { break; }
            int wnd=(sel_end-sel_beg)/wnd_part;
            int j;
            float mean;
            for (i=sel_beg;i<sel_end;i++)
            {
                data[i][2] = 0; data[i][3] = 0;
            }
            if ((cActive & 0x01)==0x01)
            {
                j = 0;
                while (j<(sel_end-sel_beg-wnd))
                {
                    mean = 0.0f;
                    for (i=sel_beg+j;i<(sel_beg+j+wnd);i++)
                    {
                        mean += data[i][0];
                        timer();
                    }
                    data[sel_beg+j+(wnd/2)][2] = mean/wnd;
                    j++;
                }
                for (i=(sel_beg+j+(wnd/2)); i<sel_end; i++) { data[i][2] = data[(sel_beg+j+(wnd/2))-1][2]; }
                for (i=sel_beg; i<(sel_beg+(wnd/2)); i++) { data[i][2] = data[sel_beg+(wnd/2)+1][2]; }
            }

            if ((cActive & 0x02)==0x02)
            {
                j = 0;
                while (j<(sel_end-sel_beg-wnd))
                {
                    mean = 0.0f;
                    for (i=sel_beg+j;i<(sel_beg+j+wnd);i++)
                    {
                        mean += data[i][1];
                        timer();
                    }
                    data[sel_beg+j+(wnd/2)][3] = mean/wnd;
                    j++;
                }
                for (i=(sel_beg+j+(wnd/2)); i<sel_end; i++) { data[i][3] = data[(sel_beg+j+(wnd/2))-1][3]; }
                for (i=sel_beg; i<(sel_beg+(wnd/2)); i++) { data[i][3] = data[sel_beg+(wnd/2)+1][3]; }
            }

            break;
        }
        case 7:     // Sliding median
        {
            if ((sel_end-sel_beg) < (wnd_part*3)) { break; }
            int wnd=(sel_end-sel_beg)/wnd_part;
            int j;
            for (i=sel_beg;i<sel_end;i++)
            {
                data[i][2] = 0; data[i][3] = 0;
            }
            if ((cActive & 0x01)==0x01)
            {
                j = 0;
                while (j<(sel_end-sel_beg-wnd))
                {
                    data[sel_beg+j+(wnd/2)][2] = get_median(sel_beg+j,sel_beg+j+wnd,0);
                    j++;
                    timer();
                }
                for (i=(sel_beg+j+(wnd/2)); i<sel_end; i++) { data[i][2] = data[(sel_beg+j+(wnd/2))-1][2]; }
                for (i=sel_beg; i<(sel_beg+(wnd/2)); i++) { data[i][2] = data[sel_beg+(wnd/2)+1][2]; }
            }

            if ((cActive & 0x02)==0x02)
            {
                j = 0;
                while (j<(sel_end-sel_beg-wnd))
                {
                    data[sel_beg+j+(wnd/2)][3] = get_median(sel_beg+j,sel_beg+j+wnd,1);
                    j++;
                    timer();
                }
                for (i=(sel_beg+j+(wnd/2)); i<sel_end; i++) { data[i][3] = data[(sel_beg+j+(wnd/2))-1][3]; }
                for (i=sel_beg; i<(sel_beg+(wnd/2)); i++) { data[i][3] = data[sel_beg+(wnd/2)+1][3]; }
            }

            break;
        }
        case 8:     // Visual shift
        {
            float k;
            float b;

            k = (vt - vf)/((float)sel_end-(float)sel_beg);  // k = (y2-y1)/(x2-x1)
            b = vf - (k*(float)sel_beg);

            if ((cActive & 0x01) == 0x01) for (i=sel_beg;i<sel_end;i++) data[i][2] = data[i][0]+(k*i + b);
            if ((cActive & 0x02) == 0x02) for (i=sel_beg;i<sel_end;i++) data[i][3] = data[i][1]+(k*i + b);
            break;
        }
        case 9:		// Visual multiplication
        {
			if ((cActive & 0x01) == 0x01) for (i=sel_beg; i<sel_end; i++) data[i][2] = data[i][0]*vt;
			if ((cActive & 0x02) == 0x02) for (i=sel_beg; i<sel_end; i++) data[i][3] = data[i][1]*vt;
			break;
		}
    }
    fBusy=0;
}

void make_undo(unsigned char sv_flg)
{
    int i;
    if ((sv_flg>0)&&(undo_count==19))
    {
        int j;
        for (j=0;j<19;j++)
        {
            for (i=0;i<86400;i++)
            {
                undo[i][0][j] = undo[i][0][j+1];
                undo[i][1][j] = undo[i][1][j+1];
            }
        }
        for (i=0;i<86400;i++)
        {
            undo[i][0][undo_count]=data[i][0];
            undo[i][1][undo_count]=data[i][1];
        }
    }
    if ((sv_flg>0)&&(undo_count<19))
    {
        undo_count++;
        for (i=0;i<86400;i++)
        {
            undo[i][0][undo_count]=data[i][0];
            undo[i][1][undo_count]=data[i][1];
        }
    }
    if ((sv_flg==0)&&(undo_count>0))
    {
        for (i=0;i<86400;i++)
        {
            data[i][0]=undo[i][0][undo_count];
            data[i][1]=undo[i][1][undo_count];
        }
        undo_count--;
    }
}

void apply_estimation(unsigned char patch)
{
    fBusy = 1;
    int i;

    make_undo(1);

    if ((selected==2)&&(est_type>0))
    {
        if ((cActive & 0x01)==0x01)
        {
            switch (patch)
            {
                case 0:
                {
                    for (i=sel_beg;i<sel_end;i++)
                    {
                        data[i][0] = data[i][2];
                        timer();
                    }
                    break;
                }
                case 1:
                {
                    for (i=sel_beg+1;i<sel_end;i++)
                    {
                        data[i][0] = (data[i][0]-data[i][2])+data[sel_beg][0];
                        timer();
                    }
                    break;
                }
            }
        }
        if ((cActive & 0x02)==0x02)
        {
            switch (patch)
            {
                case 0:
                {
                    for (i=sel_beg;i<sel_end;i++)
                    {
                        data[i][1] = data[i][3];
                        timer();
                    }
                    break;
                }
                case 1:
                {
                    for (i=sel_beg+1;i<sel_end;i++)
                    {
                        data[i][1] = (data[i][1]-data[i][3])+data[sel_beg][1];
                        timer();
                    }
                    break;
                }
            }
        }
    }
    fBusy=0;
}

void save_data()
{
    fBusy=1;
    char *sav_file_name;
    char ap_st[12]="_saved.txt";
    char zp_ap_st[9]="_zp.txt";
    int i;
    FILE *svfl;

    sav_file_name = malloc(strlen(main_file_name)+strlen(ap_st)+1);	// saving main data package
    strcpy(sav_file_name,main_file_name);
    strcat(sav_file_name,ap_st);
    svfl=fopen(sav_file_name,"wt");
    if (svfl!=NULL)
    {
        for (i=0;i<86400;i++)
        {
            fprintf(svfl,"%f\t%f\n",data[i][0],data[i][1]);
            timer();
        }
        fclose(svfl);
    }
    free (sav_file_name);
    sav_file_name=malloc(strlen(main_file_name)+strlen(zp_ap_st)+1);	// saving zero points array
    strcpy(sav_file_name,main_file_name);
    strcat(sav_file_name,zp_ap_st);
    svfl=fopen(sav_file_name,"wt");
    if (svfl!=NULL)
    {
        for (i=0;i<nzp;i++)
        {
            fprintf(svfl,"%d\t%d\t%d\t%d\t%d\n",zp[i][0],zp[i][1],zp[i][2],zp[i][3],zp[i][4]);
            timer();
        }
        fclose(svfl);
    }
	free(sav_file_name);
    fBusy=0;
}

void apply_zero_curve()	// substracts zero curve from data
{
	fBusy=1;
	int i;

	make_undo(1);

	for (i=0;i<86400;i++)	// zero line substraction
	{
		data[i][0] -= zero[i][0];
		data[i][1] -= zero[i][1];
	}

	int j;					// channel data exchange
	float tmp;
	for (i=0;i<nzp;i++) if (zp[i][4]==1)
	{
		if (i<(nzp-1)) for (j=zp[i][1];j<=zp[i+1][0];j++)
		{
			tmp=data[j][0];
			data[j][0]=data[j][1];
			data[j][1]=tmp;
		}
		else for (j=zp[i][1];j<86400;j++)
		{
			tmp=data[j][0];
			data[j][0]=data[j][1];
			data[j][1]=tmp;
		}
		timer();
	}
	if (zp[0][4]==0) for (j=0;j<=zp[0][0];j++)
	{
		tmp=data[j][0];
		data[j][0]=data[j][1];
		data[j][1]=tmp;
	}

	for (i=0;i<nzp;i++)		// linear interpolation in zero points
    {
		float k = (data[zp[i][1]][0] - data[zp[i][0]][0])/((float)zp[i][1]-(float)zp[i][0]);  // k = (y2-y1)/(x2-x1)
		float b = data[zp[i][0]][0] - (k*(float)zp[i][0]);
		for (j=zp[i][0];j<zp[i][1];j++)
		{
			data[j][0] = (k*(float)j) + b;
		}
		k = (data[zp[i][1]][1] - data[zp[i][0]][1])/((float)zp[i][1]-(float)zp[i][0]);  // k = (y2-y1)/(x2-x1)
		b = data[zp[i][0]][1] - (k*(float)zp[i][0]);
		for (j=zp[i][0];j<zp[i][1];j++)
		{
			data[j][1] = (k*(float)j) + b;
		}
		timer();
	}
	fBusy=0;
}

void make_zero_curve()	// makes zero curve from zero points data
{
	int i;
	float md1;
	float md2;
	if (nzp == 1)	// just one zero point
	{
		md1=get_median(zp[0][0]+zp[0][2],zp[0][0]+zp[0][3],0);
		md2=get_median(zp[0][0]+zp[0][2],zp[0][0]+zp[0][3],1);
		for (i=0;i<86400;i++)
		{
			zero[i][0]=md1;
			zero[i][1]=md2;
		}
	}
	if (nzp > 1)	// many zero points - linear interpolation between points
	{
		// at first we need to sort zero points array
		int j=0;
		int tmp;
		for (i=0;i<nzp-1;i++)
			for (j=i+1;j<nzp;j++)
				if (zp[i][0]>zp[j][0])
				{
					tmp=zp[i][0];
					zp[i][0]=zp[j][0];
					zp[j][0]=tmp;
					tmp=zp[i][1];
					zp[i][1]=zp[j][1];
					zp[j][1]=tmp;
				}
		md1=get_median(zp[0][0]+zp[0][2],zp[0][0]+zp[0][3],0);
		md2=get_median(zp[0][0]+zp[0][2],zp[0][0]+zp[0][3],1);
		for (i=0;i<zp[0][0];i++)	// face filling
		{
			zero[i][0]=md1;
			zero[i][1]=md2;
		}
		md1=get_median(zp[nzp-1][0]+zp[nzp-1][2],zp[nzp-1][0]+zp[nzp-1][3],0);
		md2=get_median(zp[nzp-1][0]+zp[nzp-1][2],zp[nzp-1][0]+zp[nzp-1][3],1);
		for (i=zp[nzp-1][0];i<86400;i++)	// tail filling
		{
			zero[i][0]=md1;
			zero[i][1]=md2;
		}
		float k1;
		float k2;
		float b1;
		float b2;
		float md11;
		float md21;
		for (i=0;i<(nzp-1);i++)	// linear interpolation between zero points
		{
			md1=get_median(zp[i][0]+zp[i][2],zp[i][0]+zp[i][3],0);
			md2=get_median(zp[i][0]+zp[i][2],zp[i][0]+zp[i][3],1);
			for (j=zp[i][0];j<zp[i][1];j++)
			{
				zero[j][0]=md1;
				zero[j][1]=md2;
			}
			md11=get_median(zp[i+1][0]+zp[i+1][2],zp[i+1][0]+zp[i+1][3],0);
			md21=get_median(zp[i+1][0]+zp[i+1][2],zp[i+1][0]+zp[i+1][3],1);
            k1 = (md11 - md1)/((float)zp[i+1][0]-(float)zp[i][1]);  // k = (y2-y1)/(x2-x1)
            b1 = md1 - (k1*(float)zp[i][1]);
            k2 = (md21 - md2)/((float)zp[i+1][0]-(float)zp[i][1]);  // k = (y2-y1)/(x2-x1)
            b2 = md2 - (k2*(float)zp[i][1]);
            for (j=zp[i][1];j<zp[i+1][0];j++)
            {
				zero[j][0]=k1*(float)j + b1;
				zero[j][1]=k2*(float)j + b2;
			}
		}
	}
}

void add_zero()		// Adds current selection to zero points array
{
	nzp++;
	if (nzp < 3600)
	{
		zp[nzp-1][0]=sel_beg;
		zp[nzp-1][1]=sel_end;
		zp[nzp-1][2]=50;		//TODO: maybe searching algorithm useful here???
		zp[nzp-1][3]=(sel_end-sel_beg)-30;
		if (nzp==1)
			zp[nzp-1][4] = 0; // first measure negative on first channel
		else
			zp[nzp-1][4] = 1-zp[nzp-2][4];
		selected = 0;
		make_zero_curve();
	}
	else nzp--;
}

void delete_zero(int n)	// Zero point remove routine
{
	if ((nzp>0)&&(n<nzp))
	{
		int i;
		for (i=n;i<nzp-1;i++)
		{
			zp[i][0]=zp[i+1][0];
			zp[i][1]=zp[i+1][1];
		}
		nzp--;
	}
}

int zp_at_cursor()	// returns number of zero point under cursor, or -1 if no such found
{
	int k=-1;
	int i;
	if (nzp>0) for (i=0;i<nzp;i++) if ((zp[i][0] >= wbeg)&&(zp[i][1] <= (wbeg+wsize))) // searching of zero point
	{
		if ((cpos >= zp[i][0])&&(cpos <= zp[i][1]))
		{
			k = i;
			break;
		}
	}
	return k;
}

void load_zero_points()
{
	fBusy=1;

	FILE *ldfl;

    char *ld_file_name;
    char zp_ap_st[9]="_zp.txt";

    ld_file_name = malloc(strlen(main_file_name)+strlen(zp_ap_st)+1);
    strcpy(ld_file_name,main_file_name);
    strcat(ld_file_name,zp_ap_st);
    ldfl=fopen(ld_file_name,"rt");

	if (ldfl!=NULL)
	{
		nzp=0;
		while (!feof(ldfl))
		{
			fscanf(ldfl,"%d\t%d\t%d\t%d\t%d\n",&zp[nzp][0],&zp[nzp][1],&zp[nzp][2],&zp[nzp][3],&zp[nzp][4]);
			nzp++;
			timer();
		}
		fclose(ldfl);
	}

	fBusy=0;
}

void discard_part(int poe)
{
	if (nzp >= 2)
	{
		fBusy=1;
		make_undo(1);
		int i=0;
		est_type = 1;
		while (i<nzp)
		{
			if ((zp[i][4] == poe)&&((i+1)<nzp))	cActive=1;
			if ((zp[i][4] == (1-poe))&&((i+1)<nzp)) cActive=2;
			sel_beg = zp[i][0];
			sel_end = zp[i+1][1];
			selected = 2;
			make_estimation();
			int k;
			for (k=sel_beg;k<sel_end;k++) data[k][cActive-1] = data[k][cActive+1];
			i++;
		}
		fBusy=0;
	}
}

void key_callback(GLFWwindow* wnd, int key, int scancode, int action, int mods)
{
    if ((action == GLFW_PRESS)||(action == GLFW_REPEAT))
    {
        if (nEnter==0) switch (key)
        {
            case GLFW_KEY_Q:
            {
                if (mods==GLFW_MOD_CONTROL) glfwSetWindowShouldClose(window, GL_TRUE);
                break;
            }
            case GLFW_KEY_D:
            {
                if (mods==0)
                {
                    wbeg += 600;
                    if (wbeg > (86399-wsize)) { wbeg = 86399-wsize; }
                }
                if (mods==GLFW_MOD_SHIFT)
                {
                    wsize -= 100;
                    if (wsize < 600) { wsize = 600; }
                }
                break;
            }
            case GLFW_KEY_A:
            {
                if (mods==0)
                {
                    wbeg -= 600;
                    if (wbeg < 0) { wbeg = 0; }
                }
                if (mods==GLFW_MOD_SHIFT)
                {
                    wsize += 100;
                    if (wsize > 86399) { wsize = 86399; }
                }
                if (mods==GLFW_MOD_CONTROL)
                {
					sel_beg = 0;
					sel_end = 86399;
					selected = 2;
				}
                break;
            }
            case GLFW_KEY_F1:
            {
				wsize = 3600;
				if ((wbeg+wsize)>86399) wbeg = 86399-wsize;
				break;
			}
			case GLFW_KEY_F2:
			{
				wsize = 86399;
				wbeg = 0;
				break;
			}
			case GLFW_KEY_F3:
			{
				wsize = 3600*12;
				if ((wbeg+wsize)>86399) wbeg = 86399-wsize;
				break;
			}
			case GLFW_KEY_F4:
			{
				wsize = 3600*6;
				if ((wbeg+wsize)>86399) wbeg = 86399-wsize;
				break;
			}
            case GLFW_KEY_W:
            {
                if (mods==0) { dtrim += 0.05; }
                if (mods==GLFW_MOD_SHIFT) { dscale *= 1.1; }
                if (mods==GLFW_MOD_CONTROL)
                {
                    if ((selected==2)&&((est_type==7)||(est_type==6)))
                    {
                        wnd_part += 0.1;
                        make_estimation();
                    }
                    if ((selected==2)&&((est_type==8)||(est_type==9)))
                    {
                        vf += vinc;
                        vt += vinc;
                        make_estimation();
                    }
                }
                if (mods==GLFW_MOD_ALT)
                {
                    if ((selected==2)&&(est_type==8))
                    {
                        vt += vinc;
                        make_estimation();
                    }
                }
                if (mods==(GLFW_MOD_ALT | GLFW_MOD_CONTROL))
                {
                    if ((selected==2)&&(est_type==8))
                    {
                        vf += vinc;
                        make_estimation();
                    }
                }
                break;
            }
            case GLFW_KEY_S:
            {
                if (mods==0) { dtrim -= 0.05; }
                if (mods==GLFW_MOD_SHIFT)
                {
                    dscale *= 0.9;
                }
                if (mods==GLFW_MOD_CONTROL)
                {
                    if ((selected==2)&&((est_type==7)||(est_type==6)))
                    {
                        wnd_part -= 0.1;
                        if (wnd_part < 1) { wnd_part=1; }
                        make_estimation();
                    }
                    if ((selected==2)&&((est_type==8)||(est_type==9)))
                    {
                        vf -= vinc;
                        vt -= vinc;
                        make_estimation();
                    }
                }
                if (mods==GLFW_MOD_ALT)
                {
                    if ((selected==2)&&(est_type==8))
                    {
                        vt -= vinc;
                        make_estimation();
                    }
                }
                if (mods==(GLFW_MOD_ALT | GLFW_MOD_CONTROL))
                {
                    if ((selected==2)&&(est_type==8))
                    {
                        vf -= vinc;
                        make_estimation();
                    }
                }
                break;
            }
            case GLFW_KEY_1:
            {
				if (mods==GLFW_MOD_CONTROL) discard_part(1);
			}
            case GLFW_KEY_2:
            case GLFW_KEY_3:
            case GLFW_KEY_4:
            case GLFW_KEY_5:
            case GLFW_KEY_6:
            case GLFW_KEY_7:
            case GLFW_KEY_8:
            case GLFW_KEY_9:
            {
                est_type=(int)key - (int)(GLFW_KEY_1) + 1;
                if (selected==2) { make_estimation(); }
                if ((key==GLFW_KEY_6)||(key==GLFW_KEY_7)) sprintf(name_str,"WP=");
                if ((key==GLFW_KEY_8)||(key==GLFW_KEY_9)) sprintf(name_str,"TRIM=");
                break;
            }
            case GLFW_KEY_0:
            {
                if (mods==0) est_type = 0;
				if (mods==GLFW_MOD_CONTROL) discard_part(0);
                break;
            }
            case GLFW_KEY_C:
            {
                cActive++; if (cActive>3) { cActive=1; }
                if ((est_type > 0)&&(selected==2)) { make_estimation(); }
                break;
            }
            case GLFW_KEY_F:
            {
                if (mods==GLFW_MOD_SHIFT) { apply_estimation(1); }
                if (mods==0) { apply_estimation(0); }
                break;
            }
            case GLFW_KEY_U:
            {
                make_undo(0);
                break;
            }
            case GLFW_KEY_H:
            {
                dHelp++;
                if (dHelp == 3) dHelp = 0;
                break;
            }
            case GLFW_KEY_G:
            {
                dGraph++; if (dGraph > 3) { dGraph = 1; }
                break;
            }
            case GLFW_KEY_X:
            {
				if (selected == 2)
				{
					int i;
					float tmp;
					for (i=sel_beg;i<sel_end;i++)
					{
						tmp = data[i][0];
						data[i][0]=data[i][1];
						data[i][1]=tmp;
					}
				}
//                dStatus = 1-dStatus;
                break;
            }
            case GLFW_KEY_F5:
            {
                save_data();
                break;
            }
            case GLFW_KEY_Z:
            {
            	if ((selected==2)&&(mods==0)) add_zero();
            	if (mods==GLFW_MOD_SHIFT) make_zero_curve();
            	break;
            }
            case GLFW_KEY_P:
            {
				apply_zero_curve();
				break;
			}
			case GLFW_KEY_DELETE:
			{
				int i=zp_at_cursor();
				if (i>=0) {
					delete_zero(i);
					make_zero_curve();
				}
				break;
			}
			case GLFW_KEY_I:
			{
				if (nzp>0)
				{
					int i;
					if (mods==GLFW_MOD_SHIFT) for (i=0;i<nzp;i++) zp[i][4] = 1-zp[i][4];
					else if ((i=zp_at_cursor())>=0) zp[i][4] = 1-zp[i][4];
				}
				break;
			}
			case GLFW_KEY_L:
			{
				load_zero_points();
				make_zero_curve();
				break;
			}
			case GLFW_KEY_J:
			{
				dZeroCurve = 1-dZeroCurve;
				break;
			}
			case GLFW_KEY_T:
			{
				nEnter = 1;
				sprintf(te,"%s",name_str);
				break;
			}
            default:
                key_code = key;

        }
        else switch (key)
        {
			case GLFW_KEY_0:
			case GLFW_KEY_1:
			case GLFW_KEY_2:
			case GLFW_KEY_3:
			case GLFW_KEY_4:
			case GLFW_KEY_5:
			case GLFW_KEY_6:
			case GLFW_KEY_7:
			case GLFW_KEY_8:
			case GLFW_KEY_9:
			{
				if (strlen(te)<15) sprintf(te,"%s%d",te,key-GLFW_KEY_0);
				break;
			}
			case GLFW_KEY_PERIOD:
			{
				if (strlen(te)<15) sprintf(te,"%s.",te);
				break;
			}
			case GLFW_KEY_MINUS:
			{
				int i;
				if (te[strlen(name_str)]=='-')
				{
					for (i=strlen(name_str);i<strlen(te);i++) te[i] = te[i+1];
					te[strlen(te)] = 0;
				}
				else
				{
					for (i=strlen(te);i>strlen(name_str);i--) te[i] = te[i-1];
					te[strlen(name_str)] = '-';
				}
				break;
			}
			case GLFW_KEY_BACKSPACE:
			{
				if (strlen(te)>strlen(name_str))
				{
					te[strlen(te)-1] = 0;
				}
				break;
			}
			case GLFW_KEY_ENTER:
			{
				nEnter = 0;
				if (((est_type==7)||(est_type==6))&&(selected==2))
				{
					float tfl;
					sscanf(te,"WP=%f",&tfl);
					if (tfl >= 1)
					{
						wnd_part = tfl;
						make_estimation();
					}
				}
				if (((est_type==8)||(est_type==9))&&(selected==2))
				{
					sscanf(te,"TRIM=%f",&vt);
					vf = vt;
					make_estimation();
				}
				break;
			}
			case GLFW_KEY_ESCAPE:
			{
				nEnter = 0;
				break;
			}
		}

    }
    Redisplay=1;
}

void mousemove(GLFWwindow *wnd, double x, double y)
{
    mpos = ((float)x / (screen_width/2)) - 1.0F;
    mposy = 1.0f-((float)y / (screen_height/2));
    cpos = wbeg + (int)round(((float)x / screen_width) * (float)wsize);
    Redisplay=1;
}

void mousepress(GLFWwindow *wnd, int button, int state, int mods)
{
    double x;
    double y;

    glfwGetCursorPos(wnd,&x,&y);

    if ((state==GLFW_RELEASE)&&(button==GLFW_MOUSE_BUTTON_LEFT))
    {
        if (selected==0)
        {
            sel_beg = wbeg + (int)round(((float)x / screen_width) * (float)wsize);
            selected=1;
        }
        else
        {
            if (selected==1)
            {
                sel_end = wbeg + (int)round(((float)x / screen_width) * (float)wsize);
                selected=2;
                if (sel_end < sel_beg)
                {
                    int exc;
                    exc = sel_end; sel_end = sel_beg; sel_beg = exc;
                }
                if (sel_end == sel_beg) { selected=0; }
                if (selected == 2) { make_estimation(); }
            }
        }
    }
    if ((state==GLFW_RELEASE)&&(button==GLFW_MOUSE_BUTTON_RIGHT))
    {
        selected=0;
    }
    Redisplay=1;
}

void mouseweelscroll(GLFWwindow *wnd, double xoffset, double yoffset)
{
	int k=zp_at_cursor();
	if (k>=0)
	{
		if (glfwGetKey(wnd,GLFW_KEY_LEFT_CONTROL)==GLFW_PRESS)
		{
			if (yoffset > 0) zp[k][1]++;
			if (yoffset < 0) zp[k][1]--;
			if (zp[k][1] < (zp[k][0]+zp[k][3])) zp[k][1] = zp[k][0]+zp[k][3];
			if (k==(nzp-1)) if (zp[k][1] > 86399) zp[k][1] = 86399;
			if (k<(nzp-1)) if (zp[k][1] > zp[k+1][0]) zp[k][1]=zp[k+1][0];
		}
		else if (glfwGetKey(wnd,GLFW_KEY_LEFT_SHIFT)==GLFW_PRESS)
		{
			if (yoffset > 0) zp[k][2]++;
			if (yoffset < 0) zp[k][2]--;
			if (zp[k][2] > zp[k][3]) zp[k][2] = zp[k][3];
			if (zp[k][2] < 0) zp[k][2] = 0;
		}
		else if (glfwGetKey(wnd,GLFW_KEY_LEFT_ALT)==GLFW_PRESS)
		{
			if (yoffset > 0) zp[k][3]++;
			if (yoffset < 0) zp[k][3]--;
			if (zp[k][3] > (zp[k][1]-zp[k][0])) zp[k][3] = zp[k][1]-zp[k][0];
			if (zp[k][3] < zp[k][2]) zp[k][3] = zp[k][2];
		}
		else
		{
			if (yoffset > 0) zp[k][0]++;
			if (yoffset < 0) zp[k][0]--;
			if (k==0) if (zp[k][0] < 0) zp[k][0] = 0;
			if (k>0) if (zp[k][0] < zp[k-1][1]) zp[k][0]=zp[k-1][1];
			if (zp[k][0] > (zp[k][0]+zp[k][2])) zp[k][0] = zp[k][0]+zp[k][2];
		}
	}
	make_zero_curve();
	Redisplay=1;
}

void print_usage()
{
  printf("Usage: glfw <file_name.txt>\n");
}


int main(int argc, char *argv[])
{
    FILE *f;
    int i=0;

    if ((argc<2)||(argc>2))
    {
      print_usage();
      exit(0);
    }
    main_file_name=argv[1];
    f = fopen(main_file_name,"rt");
    while (!feof(f))
    {
        fscanf(f,"%f\t%f",&data[i][0],&data[i][1]);
        i++;
    }
    fclose(f);

    for (i=0;i<86400;i++)
    {
		zero[i][0]=0;
		zero[i][1]=0;
	}

	nzp=0;
    wbeg = 0;
    wsize=3600;
    dscale=0.1;
    dtrim=0;

    load_chr_font("DRFT.CHR");

    time_start();

    if (!glfwInit())
        exit(EXIT_FAILURE);
    current_vmode = glfwGetVideoMode(glfwGetPrimaryMonitor());
    screen_width = current_vmode->width;
    screen_height = current_vmode->height;
    window = glfwCreateWindow(screen_width, screen_height, "GLFWB", glfwGetPrimaryMonitor(), NULL);
    if (!window)
    {
        glfwTerminate();
        exit(EXIT_FAILURE);
    }

    glfwMakeContextCurrent(window);
    glfwSetKeyCallback(window, key_callback);
    glfwSetMouseButtonCallback(window, mousepress);
    glfwSetCursorPosCallback(window, mousemove);
    glfwSetScrollCallback(window, mouseweelscroll);

    glClearColor(1.0,1.0,1.0,0);
    glEnable(GL_LINE_SMOOTH);
    glEnable(GL_POINT_SMOOTH);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

//---
	sprintf(name_str,"NUM=");
//---

    while (!glfwWindowShouldClose(window))
    {
        glfwPollEvents();
        if (Redisplay==1)
        {
            Draw();
            Redisplay=0;
        }
    }
    glfwDestroyWindow(window);
    glfwTerminate();

    return 0;
}
